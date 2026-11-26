/-
# P2: walking `E2E.Once` through a generated tree, step by step (line hpzg, gen 3)

`P2/OnceTree.lean` walks a tree by guarded calls (`once_step`). Here the steps that need no guard, each keeping
the run hypothesis `h` (`interp st ar (… .sbind k) s a = ok r'`) in step with the goal:

* `once_liftR`: a pure step `SProg.liftR e` (reads nothing);
* `once_ite`: an `if` on a pure condition;
* `once_rdp_q8` / `once_slotcap`: one read of a capability slot (both words), from a touched set `T` that holds
  neither word: after it the touched set is `tch (q+8) (tch q T)`;
* `q8_ne`: `q + 8 ≠ q` (so the pair's second word is not the first);
* `interp_true_of`: a run whose every leaf returns `true` returns `true`.

No premises.
-/
import Fl4Proofs.P2.OnceTree
import Fl4Proofs.P2.ProgGenL2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.E2E (Once)

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} {Rd User : U64 → Prop}

theorem q8_ne (q : U64) : core.num.U64.wrapping_add q 8#u64 ≠ q := by
  intro h
  have := congrArg UScalar.val h
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] at this
  omega

/-- **A pure step** keeps the run hypothesis. -/
theorem once_liftR {X Y : Type} {e : Result X} {k : X → SProg Y} {Wd T : Set U64} {s : S} {a : A}
    {r' : Y × S × A} (h : interp st ar ((SProg.liftR e).sbind k) s a = ok r')
    (hk : ∀ v, e = ok v → interp st ar (k v) s a = ok r' → Once st ar Rd User Wd T (k v) s a) :
    Once st ar Rd User Wd T ((SProg.liftR e).sbind k) s a := by
  unfold SProg.liftR at h ⊢
  by_cases hx : ∃ v, e = ok v
  · rw [dif_pos hx] at h ⊢
    simp only [SProg.sbind] at h ⊢
    exact hk _ hx.choose_spec h
  · rw [dif_neg hx]
    split <;> simp only [SProg.sbind, Once]

/-- **An `if` on a pure condition** keeps the run hypothesis. -/
theorem once_ite {X Y : Type} {c : Prop} [Decidable c] {p q : SProg X} {k : X → SProg Y} {Wd T : Set U64}
    {s : S} {a : A} {r' : Y × S × A} (h : interp st ar ((if c then p else q).sbind k) s a = ok r')
    (hp : c → interp st ar (p.sbind k) s a = ok r' → Once st ar Rd User Wd T (p.sbind k) s a)
    (hq : ¬ c → interp st ar (q.sbind k) s a = ok r' → Once st ar Rd User Wd T (q.sbind k) s a) :
    Once st ar Rd User Wd T ((if c then p else q).sbind k) s a := by
  by_cases hc : c
  · rw [if_pos hc] at h ⊢; exact hp hc h
  · rw [if_neg hc] at h ⊢; exact hq hc h

/-- **A guarded step** in the run-hypothesis form (`once_step` with the continuation's run). -/
theorem once_gstep {X Y : Type} {R0 W0 : U64 → Prop} (hR0 : ∀ q, R0 q → Rd q ∧ ¬ User q)
    (hW0 : ∀ q, W0 q → ¬ User q) {p : SProg X} (hz : NoZero p) {k : X → SProg Y} {Wd T : Set U64}
    {s : S} {a : A} {r' : Y × S × A} (h : interp st ar (p.sbind k) s a = ok r')
    (hg : ∀ r, interp st ar p s a = ok r → interp (guard st R0 W0) ar p s a = ok r)
    (hk : ∀ r, interp st ar p s a = ok r → interp st ar (k r.1) r.2.1 r.2.2 = ok r' →
      ∀ Wd', Wd ⊆ Wd' → Once st ar Rd User Wd' T (k r.1) r.2.1 r.2.2) :
    Once st ar Rd User Wd T (p.sbind k) s a :=
  once_step hR0 hW0 hz h hg hk

/-- **One read of a slot pair** (`obj.Slot.cap`'s tree). -/
theorem once_slotcap {Y : Type} {q : U64} {k : capability.Cap → SProg Y} {Wd T : Set U64} {s : S} {a : A}
    {r' : Y × S × A} (h : interp st ar ((R.obj.Slot.cap q).sbind k) s a = ok r')
    (h1 : E2E.Racy Rd User Wd q → q ∉ T)
    (h2 : E2E.Racy Rd User Wd (core.num.U64.wrapping_add q 8#u64) →
      core.num.U64.wrapping_add q 8#u64 ∉ E2E.tch Rd User Wd q T)
    (hk : ∀ c, obj.Slot.cap st q s = ok c → interp st ar (k c) s a = ok r' →
      Once st ar Rd User Wd (E2E.tch Rd User Wd (core.num.U64.wrapping_add q 8#u64) (E2E.tch Rd User Wd q T)) (k c) s a) :
    Once st ar Rd User Wd T ((R.obj.Slot.cap q).sbind k) s a := by
  unfold R.obj.Slot.cap at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.readPair, SProg.sbind] at h ⊢
  simp only [Once]
  refine ⟨h1, h2, fun v hv => ?_⟩
  simp only [interp] at h
  obtain ⟨v', hv', h⟩ := bok.mp h
  rw [hv] at hv'
  cases ok_inj_ff hv'
  obtain ⟨w0, w1⟩ := v
  try simp only [Std.uncurry, SProg.sbind] at h ⊢
  try dsimp only at h ⊢
  refine once_liftR h (fun c hc h' => hk c ?_ h')
  unfold obj.Slot.cap
  rw [hv]
  exact bok.mpr ⟨_, rfl, hc⟩

/-- A run of `p.sbind f` returns `true` if every run of `f` does. -/
theorem interp_true_of {X : Type} {p : SProg X} {f : X → SProg Bool} {s : S} {a : A} {r : Bool × S × A}
    (hf : ∀ x s a r, interp st ar (f x) s a = ok r → r.1 = true)
    (h : interp st ar (p.sbind f) s a = ok r) : r.1 = true := by
  rw [interp_sbind] at h
  obtain ⟨r0, -, h⟩ := bind_eq_ok' h
  exact hf _ _ _ _ h

end

end Fl4Proofs.P2.PathObl
