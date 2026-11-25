/-
# P2 (p2lf): `fire_ok`'s successor walk is `timer::remove`'s

`fire_ok_loop_eq`: from a non-null thread, `fire_ok`'s leftmost walk (`localtimer.fire_ok_loop`) is
`timer::remove`'s (`timer.remove_loop0`), on any store: the same `TIMER_LEFT` reads and the same fuel. With it,
the successor `fire_ok` checks is the value `remove` writes to `TIMER_MIN` (P1 `timer.remove.struct`), which is
what makes `fire`'s second iteration stop (`FireStop`).

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireQ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

theorem fire_ok_loop_eq {S : Type} (M : machine.Store S) (s : S) (i fuel : U64) (hi : i ≠ 0#u64) :
    localtimer.fire_ok_loop M s i fuel = timer.remove_loop0 M s i fuel := by
  unfold localtimer.fire_ok_loop timer.remove_loop0
  refine PathObl.loop_guard_congr (fun x : U64 × U64 => x.1 ≠ 0#u64) (fun x => x.2.val) ?_ (i, fuel) hi
  rintro ⟨y, f⟩ hy
  simp only at hy
  have hb : obj.Tcb.is_null y = ok false := by rw [is_null_ok]; simp [hy]
  constructor
  · simp only
    unfold localtimer.fire_ok_loop.body timer.remove_loop0.body timer.left
    rw [hb]
    simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, Std.bind_assoc]
    refine PathObl.bind_guard_congr rfl fun t _ => ?_
    rw [is_null_ok]
    by_cases h0 : t = 0#u64
    · simp [h0]
    · simp only [bind_ok, h0, decide_false, Bool.false_eq_true, ↓reduceIte, bne_iff_ne, ne_eq, not_false_eq_true]
  · rintro ⟨y', f'⟩ hc
    simp only at hc ⊢
    unfold timer.remove_loop0.body timer.left at hc
    rw [hb] at hc
    simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, Std.bind_assoc] at hc
    obtain ⟨t, _, hc⟩ := bind_eq_ok hc
    rw [is_null_ok] at hc
    simp only [bind_ok] at hc
    by_cases h0 : t = 0#u64
    · simp [h0] at hc
    · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at hc
      by_cases hf : f > 0#u64
      · simp only [hf, ↓reduceIte] at hc
        obtain ⟨f1, hf1, hc⟩ := bind_eq_ok hc
        have e := ok_inj_ff hc
        simp only [ControlFlow.cont.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        obtain ⟨g, hg, hgv⟩ := spec_ex_fd (U64.sub_spec (x := f) (y := 1#u64) (by scalar_tac))
        rw [hg] at hf1
        have := ok_inj_ff hf1
        subst this
        refine ⟨h0, ?_⟩
        have : (1#u64 : U64).val = 1 := by simp
        omega
      · simp only [hf, ↓reduceIte] at hc
        exact absurd (ok_inj_ff hc) (by simp)

end Fl4Proofs.P2
