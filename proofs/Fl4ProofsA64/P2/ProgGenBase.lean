-- AArch64 port of Fl4Proofs.P2.ProgGenBase (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
# P2: base of the generated program trees (line hpzg)

The pieces the generated modules `P2/ProgGen*.lean` (from `xtask/scripts/gen_prog.py`) build on:

* `interp_ite`, `bind_ite'`: `interp` and `Result` bind move into `if` (both sides of an equation then
  split alike); `bind_congr_r`: congruence of a bind's continuation;
* `ne_div_of_spec` and the `nd_*` facts: the pure `Result` steps the bodies take (checked arithmetic, slice
  indexing, the core-library helpers) never diverge, `interp_liftR`'s side condition;
* `AR.<m>`: each Arch-trait method as a leaf tree with its `interp` equation (from
  `xtask/scripts/gen_arch_leaves.py`), in the projection form the callers' `let (x, a') ← …` close by;
* `SProg.blk` / `bind_cut` / `BlkShape`: a non-tail sub-block (`let x ← if … / match …`) is tagged in the tree
  and the equation is cut there (no duplication of the continuation into the block's branches);
* loops: `interp_iterS` (store loops), `interp_iterSA` (store and Arch state), `interp_iterR` (read-only), with
  `cfIn` / `cfInA`; measures closed by `dec_peel` + `ge_sub1_lt` / `uadd_lt`;
* the tactics `reif_step` / `reif_loop` (equations) and `dec_peel` (measures);
* `reif_simps`: the normalisation set and `reif_nz`: the `NoZero` facts (`P2/ProgGenAttr.lean`).

No premises.
-/
import Fl4ProofsA64.P2.ProgGenAttr
import Fl4ProofsA64.P2.GuardGE
-- a64: x86_64 also imports Fl4Proofs.P1.FastFin, which nothing here uses
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P2.PathObl
open fl4_core_a64

section
variable {S : Type} {A : Type} (st : machine.Store S) (ar : machine.Arch A)

@[reif_simps] theorem interp_ite {X : Type} (c : Prop) [Decidable c] (p q : SProg X) (s : S) (a : A) :
    interp st ar (if c then p else q) s a = if c then interp st ar p s a else interp st ar q s a := by
  split <;> rfl

end

theorem bind_ite' {α β : Type} (c : Prop) [Decidable c] (x y : Result α) (f : α → Result β) :
    Aeneas.Std.bind (if c then x else y) f = if c then Aeneas.Std.bind x f else Aeneas.Std.bind y f := by
  split <;> rfl

theorem bind_congr_r {α β : Type} (m : Result α) {f g : α → Result β} (h : ∀ x, f x = g x) :
    Aeneas.Std.bind m f = Aeneas.Std.bind m g := by
  rw [funext h]

/-- Aeneas' tuple patterns (`Std.uncurry`) as projections. -/
theorem uncurry_proj {α β γ : Type} (f : α → β → γ) (x : α × β) :
    Std.uncurry f x = f x.1 x.2 := by
  cases x; rfl

theorem ite_congr' {α : Sort _} {c : Prop} [Decidable c] {a a' b b' : α} (h1 : c → a = a')
    (h2 : ¬ c → b = b') : (if c then a else b) = (if c then a' else b') := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]; exact h1 hc
  · rw [if_neg hc, if_neg hc]; exact h2 hc

theorem ite_bind_congr' {α β : Type} {c : Prop} [Decidable c] {x y : Result β} {x' y' : Result α}
    {g : α → Result β} (h1 : c → x = Aeneas.Std.bind x' g) (h2 : ¬ c → y = Aeneas.Std.bind y' g) :
    (if c then x else y) = Aeneas.Std.bind (if c then x' else y') g := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]; exact h1 hc
  · rw [if_neg hc, if_neg hc]; exact h2 hc

theorem ne_div_of_spec {α : Type} {m : Result α} {p : α → Prop} (h : m ⦃ x => p x ⦄) : m ≠ div := by
  intro e; subst e; simp [WP.spec_div] at h

/-! ## Pure steps never diverge -/

@[reif_simps] theorem nd_usub {ty : UScalarTy} (x y : UScalar ty) : (x - y : Result (UScalar ty)) ≠ div := by
  simp only [HSub.hSub, UScalar.sub]
  split
  · exact fail_not_div
  · exact ok_not_div

theorem ofOption_ne_div {α : Type} (o : Option α) (e : Error) : Result.ofOption o e ≠ div := by
  cases o <;> simp [Result.ofOption, ok_not_div, fail_not_div]

@[reif_simps] theorem nd_uadd {ty : UScalarTy} (x y : UScalar ty) : (x + y : Result (UScalar ty)) ≠ div := by
  simp only [HAdd.hAdd, UScalar.add, UScalar.tryMk]
  exact ofOption_ne_div _ _

@[reif_simps] theorem nd_umul {ty : UScalarTy} (x y : UScalar ty) : (x * y : Result (UScalar ty)) ≠ div := by
  simp only [HMul.hMul, UScalar.mul, UScalar.tryMk]
  exact ofOption_ne_div _ _

@[reif_simps] theorem nd_udiv {ty : UScalarTy} (x y : UScalar ty) : (x / y : Result (UScalar ty)) ≠ div := by
  simp only [HDiv.hDiv, UScalar.div]
  split
  · exact ok_not_div
  · exact fail_not_div

@[reif_simps] theorem nd_urem {ty : UScalarTy} (x y : UScalar ty) : (x % y : Result (UScalar ty)) ≠ div := by
  simp only [HMod.hMod, UScalar.rem]
  split
  · exact ok_not_div
  · exact fail_not_div

theorem nd_ushr_nat {ty : UScalarTy} (x : UScalar ty) (n : Nat) : x.shiftRight n ≠ div := by
  simp only [UScalar.shiftRight]
  split
  · exact ok_not_div
  · exact fail_not_div

theorem nd_ushl_nat {ty : UScalarTy} (x : UScalar ty) (n : Nat) : x.shiftLeft n ≠ div := by
  simp only [UScalar.shiftLeft]
  split
  · exact ok_not_div
  · exact fail_not_div

@[reif_simps] theorem nd_ushr_u {ty ty1 : UScalarTy} (x : UScalar ty) (y : UScalar ty1) :
    (x >>> y : Result (UScalar ty)) ≠ div := by
  simp only [HShiftRight.hShiftRight, UScalar.shiftRight_UScalar]
  exact nd_ushr_nat _ _

@[reif_simps] theorem nd_ushl_u {ty ty1 : UScalarTy} (x : UScalar ty) (y : UScalar ty1) :
    (x <<< y : Result (UScalar ty)) ≠ div := by
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar]
  exact nd_ushl_nat _ _

@[reif_simps] theorem nd_ushr_i {ty : UScalarTy} {ty1 : IScalarTy} (x : UScalar ty) (y : IScalar ty1) :
    (x >>> y : Result (UScalar ty)) ≠ div := by
  simp only [HShiftRight.hShiftRight, UScalar.shiftRight_IScalar]
  split
  · exact nd_ushr_nat _ _
  · exact fail_not_div

@[reif_simps] theorem nd_ushl_i {ty : UScalarTy} {ty1 : IScalarTy} (x : UScalar ty) (y : IScalar ty1) :
    (x <<< y : Result (UScalar ty)) ≠ div := by
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_IScalar]
  split
  · exact nd_ushl_nat _ _
  · exact fail_not_div

@[reif_simps] theorem nd_slice_index {α : Type} (v : Slice α) (i : Usize) : Slice.index_usize v i ≠ div := by
  simp only [Slice.index_usize]
  split
  · exact fail_not_div
  · exact ok_not_div

@[reif_simps] theorem nd_try_branch {T E : Type} (r : core.result.Result T E) :
    core.result.Result.Insts.CoreOpsTry.branch r ≠ div := by
  unfold core.result.Result.Insts.CoreOpsTry.branch
  split <;> exact ok_not_div

@[reif_simps] theorem nd_array_index {α : Type} {n : Usize} (v : Array α n) (i : Usize) :
    Array.index_usize v i ≠ div := by
  first
  | (unfold Array.index_usize; split <;> simp [ok_not_div, fail_not_div])
  | (simp [Array.index_usize]; split <;> simp [ok_not_div, fail_not_div])
  | simp [Array.index_usize, ok_not_div, fail_not_div]

@[reif_simps] theorem nd_array_update {α : Type} {n : Usize} (v : Array α n) (i : Usize) (x : α) :
    Array.update v i x ≠ div := by
  first
  | (unfold Array.update; split <;> simp [ok_not_div, fail_not_div])
  | (simp [Array.update]; split <;> simp [ok_not_div, fail_not_div])
  | simp [Array.update, ok_not_div, fail_not_div]

@[reif_simps] theorem nd_array_index_mut {α : Type} {n : Usize} (v : Array α n) (i : Usize) :
    Array.index_mut_usize v i ≠ div := by
  rcases result_trichotomy (Array.index_usize v i) with ⟨w, e⟩ | ⟨er, e⟩ | e
  · first
    | (simp [Array.index_mut_usize, e, ok_not_div])
    | (unfold Array.index_mut_usize; simp [e, ok_not_div])
  · first
    | (simp [Array.index_mut_usize, e, fail_not_div])
    | (unfold Array.index_mut_usize; simp [e, fail_not_div])
  · exact absurd e (nd_array_index v i)

theorem nd_from_residual {T E F : Type} (inst : core.convert.From F E) (r : core.result.Result Never E)
    (h : ∀ e, inst.from e ≠ div) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T inst r ≠ div := by
  unfold core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
  split
  · next x => cases x
  · next e =>
    rcases result_trichotomy (inst.from e) with ⟨v, he⟩ | ⟨er, he⟩ | he
    · rw [he]; simp [ok_not_div]
    · rw [he]; simp [fail_not_div]
    · exact absurd he (h e)

@[reif_simps] theorem nd_from_residual_same {T E : Type} (r : core.result.Result Never E) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T (core.convert.FromSame E) r
      ≠ div :=
  nd_from_residual _ r (fun e => by simp [core.convert.FromSame, ok_not_div])

theorem nd_ne_default {T : Type} (inst : core.cmp.PartialEq T T) (x y : T)
    (h : ∀ x y, inst.eq x y ≠ div) : core.cmp.PartialEq.ne.trait_default inst x y ≠ div := by
  unfold core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
  rcases result_trichotomy (inst.eq x y) with ⟨v, e⟩ | ⟨er, e⟩ | e
  · simp [e, ok_not_div]
  · simp [e, fail_not_div]
  · exact absurd e (h x y)

/-! ## Sub-blocks (`let x ← if … / match …` in non-tail position) -/

/-- A sub-block of a tree, tagged `k`: the generated proofs cut the equation there (`bind_cut`) instead of
pushing the continuation into the block's branches (which duplicates it). -/
def SProg.blk {V : Type} (_k : Nat) (p : SProg V) : SProg V := p

theorem NoZero.blk {V : Type} (k : Nat) {p : SProg V} (h : NoZero p) : NoZero (SProg.blk k p) := h

section
variable {S : Type} {A : Type} (st : machine.Store S) (ar : machine.Arch A)

/-- The shape of block `k`'s result: Aeneas block result to tree value, store and Arch state. -/
def BlkShape (S A : Type) (_k : Nat) (R V : Type) : Type := R → S → A → V × S × A

/-- **Cut at a sub-block**: the block's tree is the Aeneas block `Z` up to the shape `sh` (store / Arch state
before the block `s` / `a`), and the continuations agree on every block result. -/
theorem bind_cut {V R γ : Type} {k : Nat} (sh : BlkShape S A k R V) {P : SProg V} {s : S} {a : A}
    {Z : Result R} {K1 : V × S × A → Result γ} {K2 : R → Result γ}
    (h : interp st ar P s a = Aeneas.Std.bind Z (fun z => ok (sh z s a)))
    (hk : ∀ z, K1 (sh z s a) = K2 z) :
    Aeneas.Std.bind (interp st ar (SProg.blk k P) s a) K1 = Aeneas.Std.bind Z K2 := by
  show Aeneas.Std.bind (interp st ar P s a) K1 = _
  rw [h, Std.bind_assoc]
  congr 1
  funext z
  rw [bind_ok, hk]

end

/-! ## Loops over the store -/

/-- A store-only loop step's outcome in tree form (`unmk` / `unfin` split the Aeneas loop state / result into
the tree's loop value and the store state; the Arch state is unchanged). -/
def cfIn {S A X Y σ β : Type} (unmk : σ → X × S) (unfin : β → Y × S) (a : A) :
    ControlFlow σ β → Result (ControlFlow X Y × S × A)
  | .cont c => ok (.cont (unmk c).1, (unmk c).2, a)
  | .done b => ok (.done (unfin b).1, (unfin b).2, a)

attribute [reif_simps] cfIn

/-- **Store loops.** The budgeted tree loop of `bodyP` is the Aeneas loop of `body` (state `mk x s`), when
the tree body is the Aeneas body in `cfIn` form and a measure drops at every `cont` step on every store. -/
theorem interp_iterS {S A X Y σ β : Type} (st : machine.Store S) (ar : machine.Arch A)
    (body : σ → Result (ControlFlow σ β)) (bodyP : X → SProg (ControlFlow X Y))
    (mk : X → S → σ) (unmk : σ → X × S) (unfin : β → Y × S) (μ : X → Nat)
    (hmk : ∀ c, mk (unmk c).1 (unmk c).2 = c)
    (hb : ∀ x s a, interp st ar (bodyP x) s a = (body (mk x s) >>= cfIn unmk unfin a))
    (hμ : ∀ x s c, body (mk x s) = ok (.cont c) → μ (unmk c).1 < μ x) :
    ∀ n x s a, μ x < n →
      interp st ar (SProg.iter bodyP n x) s a =
        (loop body (mk x s) >>= fun b => ok ((unfin b).1, (unfin b).2, a))
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, x, s, a, h => by
    rw [SProg.iter, interp_sbind, hb, loop]
    rcases result_trichotomy (body (mk x s)) with ⟨c, e⟩ | ⟨er, e⟩ | e
    · rw [e]
      cases c with
      | cont c =>
        have ih := interp_iterS st ar body bodyP mk unmk unfin μ hmk hb hμ n (unmk c).1 (unmk c).2 a
          (Nat.lt_of_lt_of_le (hμ x s c e) (Nat.le_of_lt_succ h))
        rw [hmk] at ih
        simp only [bind_tc_eq, bind_ok, cfIn] at ih ⊢
        exact ih
      | done b => simp only [bind_tc_eq, bind_ok, cfIn, interp]
    · rw [e]; simp only [bind_tc_eq, bind_fail]
    · rw [e]; simp only [bind_tc_eq, bind_div]

/-- A loop step's outcome in tree form when the loop also threads the Arch state. -/
def cfInA {S A X Y σ β : Type} (unmk : σ → X × S × A) (unfin : β → Y × S × A) :
    ControlFlow σ β → Result (ControlFlow X Y × S × A)
  | .cont c => ok (.cont (unmk c).1, (unmk c).2.1, (unmk c).2.2)
  | .done b => ok (.done (unfin b).1, (unfin b).2.1, (unfin b).2.2)

attribute [reif_simps] cfInA

/-- **Loops over the store and the Arch state.** -/
theorem interp_iterSA {S A X Y σ β : Type} (st : machine.Store S) (ar : machine.Arch A)
    (body : σ → Result (ControlFlow σ β)) (bodyP : X → SProg (ControlFlow X Y))
    (mk : X → S → A → σ) (unmk : σ → X × S × A) (unfin : β → Y × S × A) (μ : X → Nat)
    (hmk : ∀ c, mk (unmk c).1 (unmk c).2.1 (unmk c).2.2 = c)
    (hb : ∀ x s a, interp st ar (bodyP x) s a = (body (mk x s a) >>= cfInA unmk unfin))
    (hμ : ∀ x s a c, body (mk x s a) = ok (.cont c) → μ (unmk c).1 < μ x) :
    ∀ n x s a, μ x < n →
      interp st ar (SProg.iter bodyP n x) s a =
        (loop body (mk x s a) >>= fun b => ok ((unfin b).1, (unfin b).2.1, (unfin b).2.2))
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, x, s, a, h => by
    rw [SProg.iter, interp_sbind, hb, loop]
    rcases result_trichotomy (body (mk x s a)) with ⟨c, e⟩ | ⟨er, e⟩ | e
    · rw [e]
      cases c with
      | cont c =>
        have ih := interp_iterSA st ar body bodyP mk unmk unfin μ hmk hb hμ n (unmk c).1 (unmk c).2.1
          (unmk c).2.2 (Nat.lt_of_lt_of_le (hμ x s a c e) (Nat.le_of_lt_succ h))
        rw [hmk] at ih
        simp only [bind_tc_eq, bind_ok, cfInA] at ih ⊢
        exact ih
      | done b => simp only [bind_tc_eq, bind_ok, cfInA, interp]
    · rw [e]; simp only [bind_tc_eq, bind_fail]
    · rw [e]; simp only [bind_tc_eq, bind_div]

/-- **Read-only loops** (the loop state holds no store state; the store state `s` is fixed). -/
theorem interp_iterR {S A X Y : Type} (st : machine.Store S) (ar : machine.Arch A)
    (body : X → Result (ControlFlow X Y)) (bodyP : X → SProg (ControlFlow X Y)) (μ : X → Nat) (s : S)
    (hb : ∀ x a, interp st ar (bodyP x) s a = (body x >>= fun v => ok (v, s, a)))
    (hμ : ∀ x c, body x = ok (.cont c) → μ c < μ x) :
    ∀ n x a, μ x < n →
      interp st ar (SProg.iter bodyP n x) s a = (loop body x >>= fun v => ok (v, s, a))
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, x, a, h => by
    rw [SProg.iter, interp_sbind, hb, loop]
    rcases result_trichotomy (body x) with ⟨c, e⟩ | ⟨er, e⟩ | e
    · rw [e]
      cases c with
      | cont c =>
        have ih := interp_iterR st ar body bodyP μ s hb hμ n c a
          (Nat.lt_of_lt_of_le (hμ x c e) (Nat.le_of_lt_succ h))
        simp only [bind_tc_eq, bind_ok] at ih ⊢
        exact ih
      | done b => simp only [bind_tc_eq, bind_ok, interp]
    · rw [e]; simp only [bind_tc_eq, bind_fail]
    · rw [e]; simp only [bind_tc_eq, bind_div]

/-- The proof loop of the generated equations: peel equal bind prefixes, split `match` / `if` on both sides,
normalise with `reif_simps`. -/
macro "reif_step" : tactic => `(tactic| first
  | (with_reducible apply bind_congr_r; intro)
  | (with_reducible refine ite_congr' (fun _ => ?_) (fun _ => ?_))
  | (with_reducible refine ite_bind_congr' (fun _ => ?_) (fun _ => ?_))
  | (simp only [reif_simps])
  | (with_reducible rfl)
  | (split <;> (try injections) <;> (try subst_vars))
  | contradiction
  | (simp only [SProg.blk])
  | rfl)

macro "reif_loop" : tactic => `(tactic| repeat' reif_step)

/-! ## Measures -/

theorem usize_add1_lt {n : Nat} {i j : Usize} (h : i.val < n) (e : i + 1#usize = ok j) :
    n - j.val < n - i.val := by
  have := UScalar.add_equiv i 1#usize
  rw [e] at this
  simp at this
  first | omega | scalar_tac

theorem uadd_lt {ty : UScalarTy} {i y j : UScalar ty} (e : i + y = ok j) (hy : 0 < y.val) :
    2 ^ ty.numBits - j.val < 2 ^ ty.numBits - i.val := by
  have := UScalar.add_equiv i y
  rw [e] at this
  simp at this
  have hj := j.hBounds
  first | omega | scalar_tac

theorem bind_eq_ok_std {T U : Type} {m : Result T} {f : T → Result U} {y : U}
    (h : Aeneas.Std.bind m f = ok y) : ∃ x, m = ok x ∧ f x = ok y := bind_eq_ok' h

theorem ite_eq_ok' {α : Type} {c : Prop} [Decidable c] {x y : Result α} {v : α}
    (h : (if c then x else y) = ok v) : (c ∧ x = ok v) ∨ (¬ c ∧ y = ok v) := by
  by_cases hc : c
  · exact .inl ⟨hc, by rw [if_pos hc] at h; exact h⟩
  · exact .inr ⟨hc, by rw [if_neg hc] at h; exact h⟩

theorem NoZero.ite' {X : Type} {c : Prop} [Decidable c] {p q : SProg X} (hp : NoZero p) (hq : NoZero q) :
    NoZero (if c then p else q) := by
  by_cases hc : c
  · rw [if_pos hc]; exact hp
  · rw [if_neg hc]; exact hq

theorem bind_eq_ok_iff {T U : Type} (m : Result T) (f : T → Result U) (y : U) :
    Aeneas.Std.bind m f = ok y ↔ ∃ x, m = ok x ∧ f x = ok y := by
  constructor
  · exact bind_eq_ok_std
  · rintro ⟨x, e, h⟩; rw [e, bind_ok]; exact h

theorem ite_eq_ok_iff {α : Type} (c : Prop) [Decidable c] (x y : Result α) (v : α) :
    (if c then x else y) = ok v ↔ (c ∧ x = ok v) ∨ (¬ c ∧ y = ok v) := by
  by_cases hc : c <;> simp [hc]

theorem ok_eq_ok_iff {α : Type} (a b : α) : (ok a : Result α) = ok b ↔ a = b :=
  ⟨fun h => Result.ok_injective h, fun h => h ▸ rfl⟩

theorem fail_eq_ok_iff {α : Type} (e : Error) (b : α) : (fail e : Result α) = ok b ↔ False :=
  ⟨fun h => fail_not_ok h, False.elim⟩

set_option hygiene false in
/-- Peel a `cont` hypothesis `h : body = ok (.cont σ0)` into its leaves: `simp` turns binds, `if`s and
`ok`-equations into `∃` / `∧` / `∨` (syntactic matching only, no unfolding), then `casesm` splits them. -/
macro "dec_peel" : tactic => `(tactic| (
  simp only [bind_tc_eq, lift, bind_ok, Std.bind_assoc, uncurry_proj, bind_eq_ok_iff, ite_eq_ok_iff,
    ok_eq_ok_iff, fail_eq_ok_iff, ControlFlow.cont.injEq, reduceCtorEq, false_and, and_false, false_or,
    or_false, exists_false] at h
  casesm* (_ ∧ _), (∃ _, _), (_ ∨ _)
  all_goals subst_vars))

/-- A bind with the identity in projection form. -/
theorem bind_proj3 {X S A : Type} (m : Result (X × S × A)) :
    (m >>= fun r => ok (r.1, r.2.1, r.2.2)) = m := by
  rcases result_trichotomy m with ⟨v, rfl⟩ | ⟨e, rfl⟩ | rfl
  · simp
  · simp
  · simp

/-! ## The normalisation set -/

attribute [reif_simps] SProg.bind_eq_sbind SProg.pure_eq_ret SProg.sbind interp_sbind interp_ret' interp_err'
  interp_liftR SProg.liftR_ok SProg.liftR_fail interp_read' interp_readPair' interp_write' interp_ksBase'
  interp_curCpu' interp_frameMasks' lift bind_tc_eq Std.bind_assoc bind_ok bind_fail bind_tc_ok
  bind_tc_fail not_false_eq_true ne_eq cfOut uncurry_proj

/-! ## The Arch leaves -/

section
variable {S : Type} {A : Type} (st : machine.Store S) (ar : machine.Arch A)

-- a64: the Arch leaves of AArch64 (`gen_arch_leaves.py --arch aarch64`)
def AR.private_device_frame (x0 : U64) : SProg Bool := .arch (.private_device_frame x0) fun v =>
  match v with
  | .b x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.private_device_frame_eq (x0 : U64) (s : S) (a : A) :
    interp st ar (AR.private_device_frame x0) s a = (ar.private_device_frame a x0 >>= fun v => ok (v, s, a)) := by
  rcases result_trichotomy (ar.private_device_frame a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.private_device_frame, interp, callArch, e]
@[reif_nz] theorem AR.private_device_frame_nz (x0 : U64) : NoZero (AR.private_device_frame x0) := by
  intro v; cases v <;> trivial

def AR.dma_ram (x0 : U64) (x1 : U64) : SProg Bool := .arch (.dma_ram x0 x1) fun v =>
  match v with
  | .b x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.dma_ram_eq (x0 : U64) (x1 : U64) (s : S) (a : A) :
    interp st ar (AR.dma_ram x0 x1) s a = (ar.dma_ram a x0 x1 >>= fun v => ok (v, s, a)) := by
  rcases result_trichotomy (ar.dma_ram a x0 x1) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.dma_ram, interp, callArch, e]
@[reif_nz] theorem AR.dma_ram_nz (x0 : U64) (x1 : U64) : NoZero (AR.dma_ram x0 x1) := by
  intro v; cases v <;> trivial

def AR.dma_frame (x0 : U64) (x1 : U64) (x2 : Bool) : SProg Unit := .arch (.dma_frame x0 x1 x2) fun _ => .ret ()
@[reif_simps] theorem AR.dma_frame_eq (x0 : U64) (x1 : U64) (x2 : Bool) (s : S) (a : A) :
    interp st ar (AR.dma_frame x0 x1 x2) s a = (ar.dma_frame a x0 x1 x2 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.dma_frame a x0 x1 x2) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.dma_frame, interp, callArch, e]
@[reif_nz] theorem AR.dma_frame_nz (x0 : U64) (x1 : U64) (x2 : Bool) : NoZero (AR.dma_frame x0 x1 x2) := by
  intro v; trivial

def AR.virtualization  : SProg U64 := .arch .virtualization fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.virtualization_eq  (s : S) (a : A) :
    interp st ar (AR.virtualization ) s a = (ar.virtualization a >>= fun v => ok (v, s, a)) := by
  rcases result_trichotomy (ar.virtualization a) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.virtualization, interp, callArch, e]
@[reif_nz] theorem AR.virtualization_nz  : NoZero (AR.virtualization ) := by
  intro v; cases v <;> trivial

def AR.vcpu_capability (x0 : U64) : SProg U64 := .arch (.vcpu_capability x0) fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.vcpu_capability_eq (x0 : U64) (s : S) (a : A) :
    interp st ar (AR.vcpu_capability x0) s a = (ar.vcpu_capability a x0 >>= fun v => ok (v, s, a)) := by
  rcases result_trichotomy (ar.vcpu_capability a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.vcpu_capability, interp, callArch, e]
@[reif_nz] theorem AR.vcpu_capability_nz (x0 : U64) : NoZero (AR.vcpu_capability x0) := by
  intro v; cases v <;> trivial

def AR.vcpu_barrier  : SProg Unit := .arch .vcpu_barrier fun _ => .ret ()
@[reif_simps] theorem AR.vcpu_barrier_eq  (s : S) (a : A) :
    interp st ar (AR.vcpu_barrier ) s a = (ar.vcpu_barrier a >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.vcpu_barrier a) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.vcpu_barrier, interp, callArch, e]
@[reif_nz] theorem AR.vcpu_barrier_nz  : NoZero (AR.vcpu_barrier ) := by
  intro v; trivial

def AR.vcpu_release (x0 : U64) : SProg Unit := .arch (.vcpu_release x0) fun _ => .ret ()
@[reif_simps] theorem AR.vcpu_release_eq (x0 : U64) (s : S) (a : A) :
    interp st ar (AR.vcpu_release x0) s a = (ar.vcpu_release a x0 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.vcpu_release a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.vcpu_release, interp, callArch, e]
@[reif_nz] theorem AR.vcpu_release_nz (x0 : U64) : NoZero (AR.vcpu_release x0) := by
  intro v; trivial

def AR.invalidate_ept (x0 : U64) (x1 : U64) : SProg Unit := .arch (.invalidate_ept x0 x1) fun _ => .ret ()
@[reif_simps] theorem AR.invalidate_ept_eq (x0 : U64) (x1 : U64) (s : S) (a : A) :
    interp st ar (AR.invalidate_ept x0 x1) s a = (ar.invalidate_ept a x0 x1 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.invalidate_ept a x0 x1) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.invalidate_ept, interp, callArch, e]
@[reif_nz] theorem AR.invalidate_ept_nz (x0 : U64) (x1 : U64) : NoZero (AR.invalidate_ept x0 x1) := by
  intro v; trivial

def AR.tdx_active  : SProg Bool := .arch .tdx_active fun v =>
  match v with
  | .b x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.tdx_active_eq  (s : S) (a : A) :
    interp st ar (AR.tdx_active ) s a = (ar.tdx_active a >>= fun v => ok (v, s, a)) := by
  rcases result_trichotomy (ar.tdx_active a) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.tdx_active, interp, callArch, e]
@[reif_nz] theorem AR.tdx_active_nz  : NoZero (AR.tdx_active ) := by
  intro v; cases v <;> trivial

def AR.tdx_report (x0 : U64) (x1 : U64) (x2 : U64) (x3 : U64) (x4 : U64) (x5 : U64) (x6 : U64) (x7 : U64) (x8 : U64) : SProg U64 := .arch (.tdx_report x0 x1 x2 x3 x4 x5 x6 x7 x8) fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.tdx_report_eq (x0 : U64) (x1 : U64) (x2 : U64) (x3 : U64) (x4 : U64) (x5 : U64) (x6 : U64) (x7 : U64) (x8 : U64) (s : S) (a : A) :
    interp st ar (AR.tdx_report x0 x1 x2 x3 x4 x5 x6 x7 x8) s a = (ar.tdx_report a x0 x1 x2 x3 x4 x5 x6 x7 x8 >>= fun r => ok (r.1, s, r.2)) := by
  rcases result_trichotomy (ar.tdx_report a x0 x1 x2 x3 x4 x5 x6 x7 x8) with ⟨⟨r, r2⟩, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.tdx_report, interp, callArch, e]
@[reif_nz] theorem AR.tdx_report_nz (x0 : U64) (x1 : U64) (x2 : U64) (x3 : U64) (x4 : U64) (x5 : U64) (x6 : U64) (x7 : U64) (x8 : U64) : NoZero (AR.tdx_report x0 x1 x2 x3 x4 x5 x6 x7 x8) := by
  intro v; cases v <;> trivial

def AR.tdx_extend_rtmr (x0 : U64) (x1 : U64) (x2 : U64) (x3 : U64) (x4 : U64) (x5 : U64) (x6 : U64) : SProg U64 := .arch (.tdx_extend_rtmr x0 x1 x2 x3 x4 x5 x6) fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.tdx_extend_rtmr_eq (x0 : U64) (x1 : U64) (x2 : U64) (x3 : U64) (x4 : U64) (x5 : U64) (x6 : U64) (s : S) (a : A) :
    interp st ar (AR.tdx_extend_rtmr x0 x1 x2 x3 x4 x5 x6) s a = (ar.tdx_extend_rtmr a x0 x1 x2 x3 x4 x5 x6 >>= fun r => ok (r.1, s, r.2)) := by
  rcases result_trichotomy (ar.tdx_extend_rtmr a x0 x1 x2 x3 x4 x5 x6) with ⟨⟨r, r2⟩, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.tdx_extend_rtmr, interp, callArch, e]
@[reif_nz] theorem AR.tdx_extend_rtmr_nz (x0 : U64) (x1 : U64) (x2 : U64) (x3 : U64) (x4 : U64) (x5 : U64) (x6 : U64) : NoZero (AR.tdx_extend_rtmr x0 x1 x2 x3 x4 x5 x6) := by
  intro v; cases v <;> trivial

def AR.tdx_get_quote (x0 : U64) (x1 : U64) : SProg U64 := .arch (.tdx_get_quote x0 x1) fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.tdx_get_quote_eq (x0 : U64) (x1 : U64) (s : S) (a : A) :
    interp st ar (AR.tdx_get_quote x0 x1) s a = (ar.tdx_get_quote a x0 x1 >>= fun r => ok (r.1, s, r.2)) := by
  rcases result_trichotomy (ar.tdx_get_quote a x0 x1) with ⟨⟨r, r2⟩, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.tdx_get_quote, interp, callArch, e]
@[reif_nz] theorem AR.tdx_get_quote_nz (x0 : U64) (x1 : U64) : NoZero (AR.tdx_get_quote x0 x1) := by
  intro v; cases v <;> trivial

def AR.now  : SProg U64 := .arch .now fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.now_eq  (s : S) (a : A) :
    interp st ar (AR.now ) s a = (ar.now a >>= fun r => ok (r.1, s, r.2)) := by
  rcases result_trichotomy (ar.now a) with ⟨⟨r, r2⟩, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.now, interp, callArch, e]
@[reif_nz] theorem AR.now_nz  : NoZero (AR.now ) := by
  intro v; cases v <;> trivial

def AR.set_deadline (x0 : U64) : SProg Unit := .arch (.set_deadline x0) fun _ => .ret ()
@[reif_simps] theorem AR.set_deadline_eq (x0 : U64) (s : S) (a : A) :
    interp st ar (AR.set_deadline x0) s a = (ar.set_deadline a x0 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.set_deadline a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.set_deadline, interp, callArch, e]
@[reif_nz] theorem AR.set_deadline_nz (x0 : U64) : NoZero (AR.set_deadline x0) := by
  intro v; trivial

def AR.us_to_ticks (x0 : U64) : SProg U64 := .arch (.us_to_ticks x0) fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.us_to_ticks_eq (x0 : U64) (s : S) (a : A) :
    interp st ar (AR.us_to_ticks x0) s a = (ar.us_to_ticks a x0 >>= fun v => ok (v, s, a)) := by
  rcases result_trichotomy (ar.us_to_ticks a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.us_to_ticks, interp, callArch, e]
@[reif_nz] theorem AR.us_to_ticks_nz (x0 : U64) : NoZero (AR.us_to_ticks x0) := by
  intro v; cases v <;> trivial

def AR.ticks_to_us (x0 : U64) : SProg U64 := .arch (.ticks_to_us x0) fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.ticks_to_us_eq (x0 : U64) (s : S) (a : A) :
    interp st ar (AR.ticks_to_us x0) s a = (ar.ticks_to_us a x0 >>= fun v => ok (v, s, a)) := by
  rcases result_trichotomy (ar.ticks_to_us a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.ticks_to_us, interp, callArch, e]
@[reif_nz] theorem AR.ticks_to_us_nz (x0 : U64) : NoZero (AR.ticks_to_us x0) := by
  intro v; cases v <;> trivial

def AR.max_us  : SProg U64 := .arch .max_us fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.max_us_eq  (s : S) (a : A) :
    interp st ar (AR.max_us ) s a = (ar.max_us a >>= fun v => ok (v, s, a)) := by
  rcases result_trichotomy (ar.max_us a) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.max_us, interp, callArch, e]
@[reif_nz] theorem AR.max_us_nz  : NoZero (AR.max_us ) := by
  intro v; cases v <;> trivial

def AR.kernel_wcet_ticks  : SProg U64 := .arch .kernel_wcet_ticks fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.kernel_wcet_ticks_eq  (s : S) (a : A) :
    interp st ar (AR.kernel_wcet_ticks ) s a = (ar.kernel_wcet_ticks a >>= fun v => ok (v, s, a)) := by
  rcases result_trichotomy (ar.kernel_wcet_ticks a) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.kernel_wcet_ticks, interp, callArch, e]
@[reif_nz] theorem AR.kernel_wcet_ticks_nz  : NoZero (AR.kernel_wcet_ticks ) := by
  intro v; cases v <;> trivial

def AR.irq_pending  : SProg Bool := .arch .irq_pending fun v =>
  match v with
  | .b x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.irq_pending_eq  (s : S) (a : A) :
    interp st ar (AR.irq_pending ) s a = (ar.irq_pending a >>= fun r => ok (r.1, s, r.2)) := by
  rcases result_trichotomy (ar.irq_pending a) with ⟨⟨r, r2⟩, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.irq_pending, interp, callArch, e]
@[reif_nz] theorem AR.irq_pending_nz  : NoZero (AR.irq_pending ) := by
  intro v; cases v <;> trivial

def AR.take_pending_irq  : SProg U64 := .arch .take_pending_irq fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.take_pending_irq_eq  (s : S) (a : A) :
    interp st ar (AR.take_pending_irq ) s a = (ar.take_pending_irq a >>= fun r => ok (r.1, s, r.2)) := by
  rcases result_trichotomy (ar.take_pending_irq a) with ⟨⟨r, r2⟩, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.take_pending_irq, interp, callArch, e]
@[reif_nz] theorem AR.take_pending_irq_nz  : NoZero (AR.take_pending_irq ) := by
  intro v; cases v <;> trivial

def AR.mask_irq (x0 : U64) (x1 : Bool) : SProg Unit := .arch (.mask_irq x0 x1) fun _ => .ret ()
@[reif_simps] theorem AR.mask_irq_eq (x0 : U64) (x1 : Bool) (s : S) (a : A) :
    interp st ar (AR.mask_irq x0 x1) s a = (ar.mask_irq a x0 x1 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.mask_irq a x0 x1) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.mask_irq, interp, callArch, e]
@[reif_nz] theorem AR.mask_irq_nz (x0 : U64) (x1 : Bool) : NoZero (AR.mask_irq x0 x1) := by
  intro v; trivial

def AR.ack_irq (x0 : U64) : SProg Unit := .arch (.ack_irq x0) fun _ => .ret ()
@[reif_simps] theorem AR.ack_irq_eq (x0 : U64) (s : S) (a : A) :
    interp st ar (AR.ack_irq x0) s a = (ar.ack_irq a x0 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.ack_irq a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.ack_irq, interp, callArch, e]
@[reif_nz] theorem AR.ack_irq_nz (x0 : U64) : NoZero (AR.ack_irq x0) := by
  intro v; trivial

def AR.irq_free (x0 : U64) : SProg Unit := .arch (.irq_free x0) fun _ => .ret ()
@[reif_simps] theorem AR.irq_free_eq (x0 : U64) (s : S) (a : A) :
    interp st ar (AR.irq_free x0) s a = (ar.irq_free a x0 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.irq_free a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.irq_free, interp, callArch, e]
@[reif_nz] theorem AR.irq_free_nz (x0 : U64) : NoZero (AR.irq_free x0) := by
  intro v; trivial

def AR.set_vspace (x0 : U64) (x1 : U64) : SProg Unit := .arch (.set_vspace x0 x1) fun _ => .ret ()
@[reif_simps] theorem AR.set_vspace_eq (x0 : U64) (x1 : U64) (s : S) (a : A) :
    interp st ar (AR.set_vspace x0 x1) s a = (ar.set_vspace a x0 x1 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.set_vspace a x0 x1) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.set_vspace, interp, callArch, e]
@[reif_nz] theorem AR.set_vspace_nz (x0 : U64) (x1 : U64) : NoZero (AR.set_vspace x0 x1) := by
  intro v; trivial

def AR.invalidate_page (x0 : U64) (x1 : U64) : SProg Unit := .arch (.invalidate_page x0 x1) fun _ => .ret ()
@[reif_simps] theorem AR.invalidate_page_eq (x0 : U64) (x1 : U64) (s : S) (a : A) :
    interp st ar (AR.invalidate_page x0 x1) s a = (ar.invalidate_page a x0 x1 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.invalidate_page a x0 x1) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.invalidate_page, interp, callArch, e]
@[reif_nz] theorem AR.invalidate_page_nz (x0 : U64) (x1 : U64) : NoZero (AR.invalidate_page x0 x1) := by
  intro v; trivial

def AR.invalidate_asid (x0 : U64) : SProg Unit := .arch (.invalidate_asid x0) fun _ => .ret ()
@[reif_simps] theorem AR.invalidate_asid_eq (x0 : U64) (s : S) (a : A) :
    interp st ar (AR.invalidate_asid x0) s a = (ar.invalidate_asid a x0 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.invalidate_asid a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.invalidate_asid, interp, callArch, e]
@[reif_nz] theorem AR.invalidate_asid_nz (x0 : U64) : NoZero (AR.invalidate_asid x0) := by
  intro v; trivial

def AR.invalidate_page_structures (x0 : U64) : SProg Unit := .arch (.invalidate_page_structures x0) fun _ => .ret ()
@[reif_simps] theorem AR.invalidate_page_structures_eq (x0 : U64) (s : S) (a : A) :
    interp st ar (AR.invalidate_page_structures x0) s a = (ar.invalidate_page_structures a x0 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.invalidate_page_structures a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.invalidate_page_structures, interp, callArch, e]
@[reif_nz] theorem AR.invalidate_page_structures_nz (x0 : U64) : NoZero (AR.invalidate_page_structures x0) := by
  intro v; trivial

def AR.ioapic_map (x0 : U64) (x1 : U64) (x2 : U64) (x3 : U64) (x4 : U64) : SProg Bool := .arch (.ioapic_map x0 x1 x2 x3 x4) fun v =>
  match v with
  | .b x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.ioapic_map_eq (x0 : U64) (x1 : U64) (x2 : U64) (x3 : U64) (x4 : U64) (s : S) (a : A) :
    interp st ar (AR.ioapic_map x0 x1 x2 x3 x4) s a = (ar.ioapic_map a x0 x1 x2 x3 x4 >>= fun r => ok (r.1, s, r.2)) := by
  rcases result_trichotomy (ar.ioapic_map a x0 x1 x2 x3 x4) with ⟨⟨r, r2⟩, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.ioapic_map, interp, callArch, e]
@[reif_nz] theorem AR.ioapic_map_nz (x0 : U64) (x1 : U64) (x2 : U64) (x3 : U64) (x4 : U64) : NoZero (AR.ioapic_map x0 x1 x2 x3 x4) := by
  intro v; cases v <;> trivial

def AR.ioapic_map_remapped (x0 : U64) (x1 : U64) (x2 : U64) (x3 : U64) (x4 : U64) (x5 : U64) : SProg Bool := .arch (.ioapic_map_remapped x0 x1 x2 x3 x4 x5) fun v =>
  match v with
  | .b x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.ioapic_map_remapped_eq (x0 : U64) (x1 : U64) (x2 : U64) (x3 : U64) (x4 : U64) (x5 : U64) (s : S) (a : A) :
    interp st ar (AR.ioapic_map_remapped x0 x1 x2 x3 x4 x5) s a = (ar.ioapic_map_remapped a x0 x1 x2 x3 x4 x5 >>= fun r => ok (r.1, s, r.2)) := by
  rcases result_trichotomy (ar.ioapic_map_remapped a x0 x1 x2 x3 x4 x5) with ⟨⟨r, r2⟩, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.ioapic_map_remapped, interp, callArch, e]
@[reif_nz] theorem AR.ioapic_map_remapped_nz (x0 : U64) (x1 : U64) (x2 : U64) (x3 : U64) (x4 : U64) (x5 : U64) : NoZero (AR.ioapic_map_remapped x0 x1 x2 x3 x4 x5) := by
  intro v; cases v <;> trivial

def AR.num_ioapics  : SProg U64 := .arch .num_ioapics fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.num_ioapics_eq  (s : S) (a : A) :
    interp st ar (AR.num_ioapics ) s a = (ar.num_ioapics a >>= fun v => ok (v, s, a)) := by
  rcases result_trichotomy (ar.num_ioapics a) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.num_ioapics, interp, callArch, e]
@[reif_nz] theorem AR.num_ioapics_nz  : NoZero (AR.num_ioapics ) := by
  intro v; cases v <;> trivial

def AR.ioapic_pins (x0 : U64) : SProg U64 := .arch (.ioapic_pins x0) fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.ioapic_pins_eq (x0 : U64) (s : S) (a : A) :
    interp st ar (AR.ioapic_pins x0) s a = (ar.ioapic_pins a x0 >>= fun v => ok (v, s, a)) := by
  rcases result_trichotomy (ar.ioapic_pins a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.ioapic_pins, interp, callArch, e]
@[reif_nz] theorem AR.ioapic_pins_nz (x0 : U64) : NoZero (AR.ioapic_pins x0) := by
  intro v; cases v <;> trivial

def AR.port_in (x0 : U64) (x1 : U64) : SProg U64 := .arch (.port_in x0 x1) fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.port_in_eq (x0 : U64) (x1 : U64) (s : S) (a : A) :
    interp st ar (AR.port_in x0 x1) s a = (ar.port_in a x0 x1 >>= fun r => ok (r.1, s, r.2)) := by
  rcases result_trichotomy (ar.port_in a x0 x1) with ⟨⟨r, r2⟩, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.port_in, interp, callArch, e]
@[reif_nz] theorem AR.port_in_nz (x0 : U64) (x1 : U64) : NoZero (AR.port_in x0 x1) := by
  intro v; cases v <;> trivial

def AR.port_out (x0 : U64) (x1 : U64) (x2 : U64) : SProg Unit := .arch (.port_out x0 x1 x2) fun _ => .ret ()
@[reif_simps] theorem AR.port_out_eq (x0 : U64) (x1 : U64) (x2 : U64) (s : S) (a : A) :
    interp st ar (AR.port_out x0 x1 x2) s a = (ar.port_out a x0 x1 x2 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.port_out a x0 x1 x2) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.port_out, interp, callArch, e]
@[reif_nz] theorem AR.port_out_nz (x0 : U64) (x1 : U64) (x2 : U64) : NoZero (AR.port_out x0 x1 x2) := by
  intro v; trivial

def AR.fpu_flush (x0 : U64) : SProg Unit := .arch (.fpu_flush x0) fun _ => .ret ()
@[reif_simps] theorem AR.fpu_flush_eq (x0 : U64) (s : S) (a : A) :
    interp st ar (AR.fpu_flush x0) s a = (ar.fpu_flush a x0 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.fpu_flush a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.fpu_flush, interp, callArch, e]
@[reif_nz] theorem AR.fpu_flush_nz (x0 : U64) : NoZero (AR.fpu_flush x0) := by
  intro v; trivial

def AR.fpu_sanitise (x0 : U64) : SProg Unit := .arch (.fpu_sanitise x0) fun _ => .ret ()
@[reif_simps] theorem AR.fpu_sanitise_eq (x0 : U64) (s : S) (a : A) :
    interp st ar (AR.fpu_sanitise x0) s a = (ar.fpu_sanitise a x0 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.fpu_sanitise a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.fpu_sanitise, interp, callArch, e]
@[reif_nz] theorem AR.fpu_sanitise_nz (x0 : U64) : NoZero (AR.fpu_sanitise x0) := by
  intro v; trivial

def AR.fpu_reload (x0 : U64) : SProg Unit := .arch (.fpu_reload x0) fun _ => .ret ()
@[reif_simps] theorem AR.fpu_reload_eq (x0 : U64) (s : S) (a : A) :
    interp st ar (AR.fpu_reload x0) s a = (ar.fpu_reload a x0 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.fpu_reload a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.fpu_reload, interp, callArch, e]
@[reif_nz] theorem AR.fpu_reload_nz (x0 : U64) : NoZero (AR.fpu_reload x0) := by
  intro v; trivial

def AR.fpu_release (x0 : U64) : SProg Unit := .arch (.fpu_release x0) fun _ => .ret ()
@[reif_simps] theorem AR.fpu_release_eq (x0 : U64) (s : S) (a : A) :
    interp st ar (AR.fpu_release x0) s a = (ar.fpu_release a x0 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.fpu_release a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.fpu_release, interp, callArch, e]
@[reif_nz] theorem AR.fpu_release_nz (x0 : U64) : NoZero (AR.fpu_release x0) := by
  intro v; trivial

def AR.remote_stall (x0 : U64) : SProg Unit := .arch (.remote_stall x0) fun _ => .ret ()
@[reif_simps] theorem AR.remote_stall_eq (x0 : U64) (s : S) (a : A) :
    interp st ar (AR.remote_stall x0) s a = (ar.remote_stall a x0 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.remote_stall a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.remote_stall, interp, callArch, e]
@[reif_nz] theorem AR.remote_stall_nz (x0 : U64) : NoZero (AR.remote_stall x0) := by
  intro v; trivial

def AR.send_reschedule (x0 : U128) : SProg Unit := .arch (.send_reschedule x0) fun _ => .ret ()
@[reif_simps] theorem AR.send_reschedule_eq (x0 : U128) (s : S) (a : A) :
    interp st ar (AR.send_reschedule x0) s a = (ar.send_reschedule a x0 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.send_reschedule a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.send_reschedule, interp, callArch, e]
@[reif_nz] theorem AR.send_reschedule_nz (x0 : U128) : NoZero (AR.send_reschedule x0) := by
  intro v; trivial

def AR.cache_op (x0 : U64) (x1 : U64) (x2 : U64) (x3 : U64) (x4 : U64) (x5 : U64) : SProg Unit := .arch (.cache_op x0 x1 x2 x3 x4 x5) fun _ => .ret ()
@[reif_simps] theorem AR.cache_op_eq (x0 : U64) (x1 : U64) (x2 : U64) (x3 : U64) (x4 : U64) (x5 : U64) (s : S) (a : A) :
    interp st ar (AR.cache_op x0 x1 x2 x3 x4 x5) s a = (ar.cache_op a x0 x1 x2 x3 x4 x5 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.cache_op a x0 x1 x2 x3 x4 x5) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.cache_op, interp, callArch, e]
@[reif_nz] theorem AR.cache_op_nz (x0 : U64) (x1 : U64) (x2 : U64) (x3 : U64) (x4 : U64) (x5 : U64) : NoZero (AR.cache_op x0 x1 x2 x3 x4 x5) := by
  intro v; trivial

def AR.hw_access_flag  : SProg Bool := .arch .hw_access_flag fun v =>
  match v with
  | .b x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.hw_access_flag_eq  (s : S) (a : A) :
    interp st ar (AR.hw_access_flag ) s a = (ar.hw_access_flag a >>= fun v => ok (v, s, a)) := by
  rcases result_trichotomy (ar.hw_access_flag a) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.hw_access_flag, interp, callArch, e]
@[reif_nz] theorem AR.hw_access_flag_nz  : NoZero (AR.hw_access_flag ) := by
  intro v; cases v <;> trivial

def AR.max_spi  : SProg U64 := .arch .max_spi fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.max_spi_eq  (s : S) (a : A) :
    interp st ar (AR.max_spi ) s a = (ar.max_spi a >>= fun v => ok (v, s, a)) := by
  rcases result_trichotomy (ar.max_spi a) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.max_spi, interp, callArch, e]
@[reif_nz] theorem AR.max_spi_nz  : NoZero (AR.max_spi ) := by
  intro v; cases v <;> trivial

def AR.configure_irq (x0 : U64) (x1 : Bool) (x2 : U64) : SProg Unit := .arch (.configure_irq x0 x1 x2) fun _ => .ret ()
@[reif_simps] theorem AR.configure_irq_eq (x0 : U64) (x1 : Bool) (x2 : U64) (s : S) (a : A) :
    interp st ar (AR.configure_irq x0 x1 x2) s a = (ar.configure_irq a x0 x1 x2 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.configure_irq a x0 x1 x2) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.configure_irq, interp, callArch, e]
@[reif_nz] theorem AR.configure_irq_nz (x0 : U64) (x1 : Bool) (x2 : U64) : NoZero (AR.configure_irq x0 x1 x2) := by
  intro v; trivial

def AR.msi_map (x0 : U64) (x1 : U64) (x2 : U64) (x3 : U64) : SProg U64 := .arch (.msi_map x0 x1 x2 x3) fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.msi_map_eq (x0 : U64) (x1 : U64) (x2 : U64) (x3 : U64) (s : S) (a : A) :
    interp st ar (AR.msi_map x0 x1 x2 x3) s a = (ar.msi_map a x0 x1 x2 x3 >>= fun r => ok (r.1, s, r.2)) := by
  rcases result_trichotomy (ar.msi_map a x0 x1 x2 x3) with ⟨⟨r, r2⟩, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.msi_map, interp, callArch, e]
@[reif_nz] theorem AR.msi_map_nz (x0 : U64) (x1 : U64) (x2 : U64) (x3 : U64) : NoZero (AR.msi_map x0 x1 x2 x3) := by
  intro v; cases v <;> trivial

def AR.s2_ipa_bits  : SProg U64 := .arch .s2_ipa_bits fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.s2_ipa_bits_eq  (s : S) (a : A) :
    interp st ar (AR.s2_ipa_bits ) s a = (ar.s2_ipa_bits a >>= fun v => ok (v, s, a)) := by
  rcases result_trichotomy (ar.s2_ipa_bits a) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.s2_ipa_bits, interp, callArch, e]
@[reif_nz] theorem AR.s2_ipa_bits_nz  : NoZero (AR.s2_ipa_bits ) := by
  intro v; cases v <;> trivial

def AR.set_stage2_vspace (x0 : U64) (x1 : U64) : SProg Unit := .arch (.set_stage2_vspace x0 x1) fun _ => .ret ()
@[reif_simps] theorem AR.set_stage2_vspace_eq (x0 : U64) (x1 : U64) (s : S) (a : A) :
    interp st ar (AR.set_stage2_vspace x0 x1) s a = (ar.set_stage2_vspace a x0 x1 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.set_stage2_vspace a x0 x1) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.set_stage2_vspace, interp, callArch, e]
@[reif_nz] theorem AR.set_stage2_vspace_nz (x0 : U64) (x1 : U64) : NoZero (AR.set_stage2_vspace x0 x1) := by
  intro v; trivial

def AR.invalidate_stage2_page (x0 : U64) (x1 : U64) : SProg Unit := .arch (.invalidate_stage2_page x0 x1) fun _ => .ret ()
@[reif_simps] theorem AR.invalidate_stage2_page_eq (x0 : U64) (x1 : U64) (s : S) (a : A) :
    interp st ar (AR.invalidate_stage2_page x0 x1) s a = (ar.invalidate_stage2_page a x0 x1 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.invalidate_stage2_page a x0 x1) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.invalidate_stage2_page, interp, callArch, e]
@[reif_nz] theorem AR.invalidate_stage2_page_nz (x0 : U64) (x1 : U64) : NoZero (AR.invalidate_stage2_page x0 x1) := by
  intro v; trivial

def AR.invalidate_stage2_vmid (x0 : U64) : SProg Unit := .arch (.invalidate_stage2_vmid x0) fun _ => .ret ()
@[reif_simps] theorem AR.invalidate_stage2_vmid_eq (x0 : U64) (s : S) (a : A) :
    interp st ar (AR.invalidate_stage2_vmid x0) s a = (ar.invalidate_stage2_vmid a x0 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.invalidate_stage2_vmid a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.invalidate_stage2_vmid, interp, callArch, e]
@[reif_nz] theorem AR.invalidate_stage2_vmid_nz (x0 : U64) : NoZero (AR.invalidate_stage2_vmid x0) := by
  intro v; trivial

def AR.vcpu_flush (x0 : U64) : SProg Unit := .arch (.vcpu_flush x0) fun _ => .ret ()
@[reif_simps] theorem AR.vcpu_flush_eq (x0 : U64) (s : S) (a : A) :
    interp st ar (AR.vcpu_flush x0) s a = (ar.vcpu_flush a x0 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.vcpu_flush a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.vcpu_flush, interp, callArch, e]
@[reif_nz] theorem AR.vcpu_flush_nz (x0 : U64) : NoZero (AR.vcpu_flush x0) := by
  intro v; trivial

def AR.vcpu_flush_state (x0 : U64) (x1 : U64) : SProg Unit := .arch (.vcpu_flush_state x0 x1) fun _ => .ret ()
@[reif_simps] theorem AR.vcpu_flush_state_eq (x0 : U64) (x1 : U64) (s : S) (a : A) :
    interp st ar (AR.vcpu_flush_state x0 x1) s a = (ar.vcpu_flush_state a x0 x1 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.vcpu_flush_state a x0 x1) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.vcpu_flush_state, interp, callArch, e]
@[reif_nz] theorem AR.vcpu_flush_state_nz (x0 : U64) (x1 : U64) : NoZero (AR.vcpu_flush_state x0 x1) := by
  intro v; trivial

def AR.vcpu_vgic_vtr  : SProg U64 := .arch .vcpu_vgic_vtr fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.vcpu_vgic_vtr_eq  (s : S) (a : A) :
    interp st ar (AR.vcpu_vgic_vtr ) s a = (ar.vcpu_vgic_vtr a >>= fun v => ok (v, s, a)) := by
  rcases result_trichotomy (ar.vcpu_vgic_vtr a) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.vcpu_vgic_vtr, interp, callArch, e]
@[reif_nz] theorem AR.vcpu_vgic_vtr_nz  : NoZero (AR.vcpu_vgic_vtr ) := by
  intro v; cases v <;> trivial

def AR.vcpu_gic_version  : SProg U64 := .arch .vcpu_gic_version fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.vcpu_gic_version_eq  (s : S) (a : A) :
    interp st ar (AR.vcpu_gic_version ) s a = (ar.vcpu_gic_version a >>= fun v => ok (v, s, a)) := by
  rcases result_trichotomy (ar.vcpu_gic_version a) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.vcpu_gic_version, interp, callArch, e]
@[reif_nz] theorem AR.vcpu_gic_version_nz  : NoZero (AR.vcpu_gic_version ) := by
  intro v; cases v <;> trivial

def AR.vcpu_midr  : SProg U64 := .arch .vcpu_midr fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.vcpu_midr_eq  (s : S) (a : A) :
    interp st ar (AR.vcpu_midr ) s a = (ar.vcpu_midr a >>= fun v => ok (v, s, a)) := by
  rcases result_trichotomy (ar.vcpu_midr a) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.vcpu_midr, interp, callArch, e]
@[reif_nz] theorem AR.vcpu_midr_nz  : NoZero (AR.vcpu_midr ) := by
  intro v; cases v <;> trivial

def AR.has_pauth  : SProg Bool := .arch .has_pauth fun v =>
  match v with
  | .b x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.has_pauth_eq  (s : S) (a : A) :
    interp st ar (AR.has_pauth ) s a = (ar.has_pauth a >>= fun v => ok (v, s, a)) := by
  rcases result_trichotomy (ar.has_pauth a) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.has_pauth, interp, callArch, e]
@[reif_nz] theorem AR.has_pauth_nz  : NoZero (AR.has_pauth ) := by
  intro v; cases v <;> trivial

def AR.next_pac_epoch  : SProg U64 := .arch .next_pac_epoch fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.next_pac_epoch_eq  (s : S) (a : A) :
    interp st ar (AR.next_pac_epoch ) s a = (ar.next_pac_epoch a >>= fun r => ok (r.1, s, r.2)) := by
  rcases result_trichotomy (ar.next_pac_epoch a) with ⟨⟨r, r2⟩, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.next_pac_epoch, interp, callArch, e]
@[reif_nz] theorem AR.next_pac_epoch_nz  : NoZero (AR.next_pac_epoch ) := by
  intro v; cases v <;> trivial

def AR.kernel_ttbr1_entry (x0 : U64) (x1 : U64) : SProg U64 := .arch (.kernel_ttbr1_entry x0 x1) fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.kernel_ttbr1_entry_eq (x0 : U64) (x1 : U64) (s : S) (a : A) :
    interp st ar (AR.kernel_ttbr1_entry x0 x1) s a = (ar.kernel_ttbr1_entry a x0 x1 >>= fun v => ok (v, s, a)) := by
  rcases result_trichotomy (ar.kernel_ttbr1_entry a x0 x1) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.kernel_ttbr1_entry, interp, callArch, e]
@[reif_nz] theorem AR.kernel_ttbr1_entry_nz (x0 : U64) (x1 : U64) : NoZero (AR.kernel_ttbr1_entry x0 x1) := by
  intro v; cases v <;> trivial

def AR.set_high_vspace (x0 : U64) (x1 : U64) : SProg Unit := .arch (.set_high_vspace x0 x1) fun _ => .ret ()
@[reif_simps] theorem AR.set_high_vspace_eq (x0 : U64) (x1 : U64) (s : S) (a : A) :
    interp st ar (AR.set_high_vspace x0 x1) s a = (ar.set_high_vspace a x0 x1 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.set_high_vspace a x0 x1) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.set_high_vspace, interp, callArch, e]
@[reif_nz] theorem AR.set_high_vspace_nz (x0 : U64) (x1 : U64) : NoZero (AR.set_high_vspace x0 x1) := by
  intro v; trivial

def AR.invalidate_high_page (x0 : U64) : SProg Unit := .arch (.invalidate_high_page x0) fun _ => .ret ()
@[reif_simps] theorem AR.invalidate_high_page_eq (x0 : U64) (s : S) (a : A) :
    interp st ar (AR.invalidate_high_page x0) s a = (ar.invalidate_high_page a x0 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.invalidate_high_page a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.invalidate_high_page, interp, callArch, e]
@[reif_nz] theorem AR.invalidate_high_page_nz (x0 : U64) : NoZero (AR.invalidate_high_page x0) := by
  intro v; trivial

def AR.invalidate_high_vspace (x0 : U64) : SProg Unit := .arch (.invalidate_high_vspace x0) fun _ => .ret ()
@[reif_simps] theorem AR.invalidate_high_vspace_eq (x0 : U64) (s : S) (a : A) :
    interp st ar (AR.invalidate_high_vspace x0) s a = (ar.invalidate_high_vspace a x0 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.invalidate_high_vspace a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.invalidate_high_vspace, interp, callArch, e]
@[reif_nz] theorem AR.invalidate_high_vspace_nz (x0 : U64) : NoZero (AR.invalidate_high_vspace x0) := by
  intro v; trivial

def AR.putc (x0 : U64) : SProg Unit := .arch (.putc x0) fun _ => .ret ()
@[reif_simps] theorem AR.putc_eq (x0 : U64) (s : S) (a : A) :
    interp st ar (AR.putc x0) s a = (ar.putc a x0 >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.putc a x0) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.putc, interp, callArch, e]
@[reif_nz] theorem AR.putc_nz (x0 : U64) : NoZero (AR.putc x0) := by
  intro v; trivial

def AR.get_char  : SProg U64 := .arch .get_char fun v =>
  match v with
  | .u x => .ret x
  | _ => .err .panic
@[reif_simps] theorem AR.get_char_eq  (s : S) (a : A) :
    interp st ar (AR.get_char ) s a = (ar.get_char a >>= fun r => ok (r.1, s, r.2)) := by
  rcases result_trichotomy (ar.get_char a) with ⟨⟨r, r2⟩, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.get_char, interp, callArch, e]
@[reif_nz] theorem AR.get_char_nz  : NoZero (AR.get_char ) := by
  intro v; cases v <;> trivial

def AR.halt  : SProg Unit := .arch .halt fun _ => .ret ()
@[reif_simps] theorem AR.halt_eq  (s : S) (a : A) :
    interp st ar (AR.halt ) s a = (ar.halt a >>= fun a' => ok ((), s, a')) := by
  rcases result_trichotomy (ar.halt a) with ⟨r, e⟩ | ⟨er, e⟩ | e <;>
    simp [AR.halt, interp, callArch, e]
@[reif_nz] theorem AR.halt_nz  : NoZero (AR.halt ) := by
  intro v; trivial

end

end Fl4ProofsA64.P2.PathObl
