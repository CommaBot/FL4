/-
P2 (regression example): **`IsProg` does not fix how often a body reads a word.**

`machine.Store.read` returns no state, so on every store instance two reads of a
word with no write between agree. A body that reads a word twice and compares
(`twice`) is therefore `IsProg` both of its own tree (`pTwice`, two reads) and
of the tree that reads once and answers `true` (`pOnce`). Run beside other
cores, only the first can see the word change between its reads. `E2E.ReadOnce`
holds of `pOnce` and not of `pTwice` (for a racy word), so it can be proved "of
a body" by choosing the wrong tree: the tree in a `LocalPath` must be the body's
own sequence of trait calls, as `IsProg`'s docstring says ([P]); its statement
alone does not force it.
-/
import Fl4Proofs.P2.E2E
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.ReadGap
open fl4_core Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2E

noncomputable section
open Classical

variable {S : Type}

/-- Read word 0 twice, and say whether the values agree. -/
def twice {A : Type} (_ : machine.Arch A) (st : machine.Store S) (s : S) (a : A) :
    Result (Bool × S × A) := do
  let v ← st.read s 0#u64
  let w ← st.read s 0#u64
  ok (decide (v = w), s, a)

/-- Its own tree. -/
def pTwice : SProg Bool := .rd 0#u64 fun v => .rd 0#u64 fun w => .ret (decide (v = w))

/-- A tree that reads once. -/
def pOnce : SProg Bool := .rd 0#u64 fun _ => .ret true

theorem isProg_pTwice : IsProg (S := S) twice pTwice := fun _ _ _ => rfl

theorem bind_congr {α β : Type} (m : Result α) (f g : α → Result β)
    (h : ∀ v, m = ok v → f v = g v) : (m >>= f) = (m >>= g) := by
  cases m with
  | ret v => rw [bind_tc_ok, bind_tc_ok]; exact h v rfl
  | vis e k =>
    rw [bind_tc_vis, bind_tc_vis]
    congr 1
    funext x
    cases e
    exact PEmpty.elim x
  | div => rw [bind_tc_div, bind_tc_div]

theorem isProg_pOnce : IsProg (S := S) twice pOnce := by
  intro A ar st
  funext s a
  refine bind_congr (st.read s 0#u64) _ _ fun v hv => ?_
  beta_reduce
  rw [hv]
  simp [interp]

/-- `pOnce` reads once, `pTwice` does not (word 0 racy). -/
theorem once_pOnce {A : Type} (st : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) :
    Once st ar (fun _ => False) (fun _ => False) ∅ ∅ pOnce s a := by
  simp only [pOnce, Once]
  exact ⟨fun _ h => absurd h (Set.notMem_empty _), fun _ _ => trivial⟩

theorem not_once_pTwice {A : Type} (st : machine.Store S) (ar : machine.Arch A) (s : S) (a : A)
    {v : U64} (hv : st.read s 0#u64 = ok v) :
    ¬ Once st ar (fun _ => False) (fun _ => False) ∅ ∅ pTwice s a := by
  intro h
  simp only [pTwice, Once] at h
  have hr : Racy (fun _ => False) (fun _ => False) (∅ : Set U64) 0#u64 :=
    fun h => h.2.elim id (Set.notMem_empty _)
  have h1 := (h.2 v hv).1 hr
  apply h1
  unfold tch
  rw [if_pos hr]
  exact Set.mem_insert _ _

end
end Fl4Proofs.P2.ReadGap
