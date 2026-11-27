/-
# P2 (p2lf): who `schedule` picks after a wake

After the woken thread's action, `schedule` may re-queue the current thread `ct` and queue the woken thread `w`
(`enqueue`: at the head; `append`: at the tail) before `choose_thread` takes the head of the highest non-empty ready
queue. `pick_top` (on the ghost queues alone): if every queue after the re-queues `Q'` is the queue before `Q`, or
has `ct` or `w` at its head, or kept a non-empty queue's head, and no non-empty queue became empty, then the head of
the highest non-empty queue of `Q'` is `ct`, `w`, or the head of a queue of `Q` at the same priority that is also
the highest of `Q` (the head `top_ok` checked, the ready queues being unchanged between `fire_ok` and `schedule`).

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireWc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2

/-- **The head `choose_thread` takes after the re-queues** (module docstring). -/
theorem pick_top {Q Q' : U64 → List U64} {ct w h' : U64}
    (hmono : ∀ p : U64, p.val < 256 → Q p ≠ [] → Q' p ≠ [])
    (hshape : ∀ p : U64, p.val < 256 → Q' p ≠ [] → Q' p = Q p ∨ (Q' p).head? = some ct ∨
      (Q' p).head? = some w ∨ (Q p ≠ [] ∧ (Q' p).head? = (Q p).head?))
    (hh' : h'.val < 256) (hne' : Q' h' ≠ [])
    (hmax' : ∀ p : U64, p.val < 256 → Q' p ≠ [] → p.val ≤ h'.val) :
    (Q' h').head? = some ct ∨ (Q' h').head? = some w ∨
      (Q h' ≠ [] ∧ (Q' h').head? = (Q h').head? ∧ ∀ p : U64, p.val < 256 → Q p ≠ [] → p.val ≤ h'.val) := by
  have top : ∀ p : U64, p.val < 256 → Q p ≠ [] → p.val ≤ h'.val := fun p hp hq => hmax' p hp (hmono p hp hq)
  rcases hshape h' hh' hne' with e | e | e | ⟨hq, e⟩
  · exact Or.inr (Or.inr ⟨by rw [← e]; exact hne', by rw [e], top⟩)
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr ⟨hq, e, top⟩)

/-- The head of a highest non-empty queue is unique: two highest non-empty priorities are equal. -/
theorem top_unique {Q : U64 → List U64} {h h' : U64} (hh : h.val < 256) (hh' : h'.val < 256)
    (hne : Q h ≠ []) (hne' : Q h' ≠ [])
    (hmax : ∀ p : U64, p.val < 256 → Q p ≠ [] → p.val ≤ h.val)
    (hmax' : ∀ p : U64, p.val < 256 → Q p ≠ [] → p.val ≤ h'.val) : h = h' :=
  UScalar.eq_of_val_eq (Nat.le_antisymm (hmax' h hh hne) (hmax h' hh' hne'))

section
open fl4_core Fl4Proofs.P1
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

/-- **`choose_thread` takes the head of the highest non-empty ready queue** (P1 `choose_thread_eq_pick` with
`highest_prio.spec`), at a state whose ready queues of this core hold `Q'`, one of them non-empty. -/
theorem choose_head {A : Type} (ar : machine.Arch A) {Z : S} {Q' : U64 → List U64}
    (hN : NodePlaced st T Z (L.cpu Z)) (hRQ : ReadyQueues st T Z (L.cpu Z) Q') {p0 : U64} (hp0 : p0.val < 256)
    (hne0 : Q' p0 ≠ []) :
    ∃ h' : U64, h'.val < 256 ∧ Q' h' ≠ [] ∧ (∀ p : U64, p.val < 256 → Q' p ≠ [] → p.val ≤ h'.val) ∧
      L.l1W Z (L.cpu Z) ≠ 0#u64 ∧ sched.highest_prio st Z 0#u64 = ok h' ∧
      L.mem Z (L.nodeAt Z (L.cpu Z) (rqOff h')) = (Q' h').headD 0#u64 ∧
      ∀ a : A, sched.choose_thread st ar Z a = sched.switch_to_thread st ar Z a ((Q' h').headD 0#u64) := by
  obtain ⟨hR, hB⟩ := hRQ
  have hl1 : L.l1W Z (L.cpu Z) ≠ 0#u64 := by
    have hb := (hB.l2 p0 hp0).2 hne0
    have hw : L.l2W Z (L.cpu Z) (p0.val / 64) ≠ 0#u64 := (ne_zero_iff_bit _).2 ⟨_, by omega, hb⟩
    have hl := (hB.l1 (p0.val / 64) (by omega)).2 ⟨by omega, hw⟩
    exact (ne_zero_iff_bit _).2 ⟨_, by omega, hl⟩
  obtain ⟨q, hq, hq1, hq2, hq3⟩ := spec_ex_fd (sched.highest_prio.spec (L := L) Z 0#u64 _ hN hB hl1)
  have eh : L.mem Z (L.nodeAt Z (L.cpu Z) (rqOff q)) = (Q' q).headD 0#u64 := (hR.rel q hq1).head
  refine ⟨q, hq1, hq2, hq3, hl1, hq, eh, fun a => ?_⟩
  rw [choose_thread_eq_pick ar Z a hq1 hl1 hq, eh]

end

end Fl4Proofs.P2
