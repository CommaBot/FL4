/-
# P2: a run on a guarded store makes no racy read

`once_of_guardG`: a run of a tree `p` without `zero` / `clr` on `PathObl.guard st R W`, `R` holding
no user word, satisfies `E2E.Once` for `R`: every read is of an `R` word, which is not racy.
(The same statement as p2e's `once_of_guard` in `P2/AccessVmObl.lean`, kept here under its own
name so the lines merge without a clash.)

No premises.
-/
import Fl4Proofs.P2.E2E
import Fl4Proofs.P2.PathBridge
import Fl4Proofs.P1.FastFin
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.E2E (Once)

/-! ## A guarded run makes no racy read -/

section once
open Classical
variable {S A X : Type} {st : machine.Store S} {ar : machine.Arch A} {R W : U64 → Prop}

/-- **A run on `PathObl.guard st R W` reads only `R` words**, so with no user word in `R` it reads no racy word. -/
theorem once_of_guardG {User : U64 → Prop} (hU : ∀ q, R q → ¬ User q) (p : SProg X) (hz : NoZero p) :
    ∀ (Wd T : Set U64) (s : S) (a : A) (r : X × S × A), interp (PathObl.guard st R W) ar p s a = ok r →
      Once st ar R User Wd T p s a := by
  induction p with
  | ret x => intro Wd T s a r _; simp only [Once]
  | err e => intro Wd T s a r h; exact absurd h fail_not_ok
  | rd q k ih =>
    intro Wd T s a r h
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    by_cases hq : R q
    · rw [guard_read hq] at hv
      simp only [Once]
      refine ⟨fun hr => absurd (show ¬ User q ∧ (R q ∨ q ∈ Wd) from ⟨hU q hq, Or.inl hq⟩) hr, fun v' hv' => ?_⟩
      rw [hv] at hv'
      have e := ok_inj_ff hv'
      subst e
      exact ih _ (hz _) _ _ s a r hk
    · rw [guard_read_out hq] at hv; exact absurd hv fail_not_ok
  | rdp q k ih =>
    intro Wd T s a r h
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    by_cases hq : R q ∧ R (core.num.U64.wrapping_add q 8#u64)
    · rw [guard_read_pair hq.1 hq.2] at hv
      simp only [Once]
      refine ⟨fun hr => absurd (show ¬ User q ∧ (R q ∨ q ∈ Wd) from ⟨hU q hq.1, Or.inl hq.1⟩) hr,
        fun hr => absurd (show ¬ User (core.num.U64.wrapping_add q 8#u64) ∧
          (R (core.num.U64.wrapping_add q 8#u64) ∨ core.num.U64.wrapping_add q 8#u64 ∈ Wd) from
            ⟨hU _ hq.2, Or.inl hq.2⟩) hr, fun v' hv' => ?_⟩
      rw [hv] at hv'
      have e := ok_inj_ff hv'
      subst e
      exact ih _ (hz _) _ _ s a r hk
    · have : (PathObl.guard st R W).read_pair s q = fail .panic := by
        show (if R q ∧ R (core.num.U64.wrapping_add q 8#u64) then st.read_pair s q else fail .panic) = _
        rw [if_neg hq]
      rw [this] at hv; exact absurd hv fail_not_ok
  | wr q v k ih =>
    intro Wd T s a r h
    simp only [interp] at h
    obtain ⟨s', hv, hk⟩ := bok.mp h
    by_cases hq : W q
    · rw [guard_write hq] at hv
      simp only [Once]
      intro s'' hs''
      rw [hv] at hs''
      have e := ok_inj_ff hs''
      subst e
      exact ih hz _ _ _ a r hk
    · rw [guard_write_out hq] at hv; exact absurd hv fail_not_ok
  | zero q n k ih => exact absurd hz id
  | clr q n k ih => exact absurd hz id
  | ksb k ih =>
    intro Wd T s a r h
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv2 : st.ks_base s = ok v := hv
    simp only [Once]
    intro v' hv'
    rw [hv2] at hv'
    have e := ok_inj_ff hv'
    subst e
    exact ih _ (hz _) _ _ s a r hk
  | cpu k ih =>
    intro Wd T s a r h
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv2 : st.cur_cpu s = ok v := hv
    simp only [Once]
    intro v' hv'
    rw [hv2] at hv'
    have e := ok_inj_ff hv'
    subst e
    exact ih _ (hz _) _ _ s a r hk
  | masks k ih =>
    intro Wd T s a r h
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv2 : st.frame_masks s = ok v := hv
    simp only [Once]
    intro v' hv'
    rw [hv2] at hv'
    have e := ok_inj_ff hv'
    subst e
    exact ih _ (hz _) _ _ s a r hk
  | arch op k ih =>
    intro Wd T s a r h
    simp only [interp] at h
    obtain ⟨⟨v, a'⟩, hv, hk⟩ := bok.mp h
    simp only [Once]
    intro v' a'' hv'
    rw [hv] at hv'
    obtain ⟨e1, e2⟩ := Prod.mk.inj (ok_inj_ff hv')
    subst e1
    subst e2
    exact ih _ (hz _) _ _ s _ r hk

end once

end Fl4Proofs.P2.PathObl
