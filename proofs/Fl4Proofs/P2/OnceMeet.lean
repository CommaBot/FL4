/-
# P2 (line invj, generation 8): `Once` moves to another read set along a guarded run

**`once_meetG`**: if a run of a tree `p` (no `zero` / `clr`) on `PathObl.guard st G W` succeeds, and `p` satisfies
`E2E.Once` for the read set `R` from `s`, then it satisfies `Once` for every `R'` that contains the `R` words the
run may read (`G q → R q → R' q`), from any smaller touched set. A read is of a `G` word, and such a word that is
racy for `R'` is racy for `R`.

(Used where the read set of a path shrinks to drop words the run never reads: the Delete PTE arm's `InvRSP` drops
the unlocked leaf entries from `InvCMRS`, P2/InvDelPteOnceP.lean.) No premise. New module.
-/
import Fl4Proofs.P2.OnceGuard
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.E2E (Once)

section meet
open Classical
variable {S A X : Type} {st : machine.Store S} {ar : machine.Arch A} {R R' G W User : U64 → Prop}

theorem racy_meet (hR : ∀ q, G q → R q → R' q) {Wd : Set U64} {q : U64} (hq : G q)
    (h : E2E.Racy R' User Wd q) : E2E.Racy R User Wd q := by
  unfold E2E.Racy at *
  rintro ⟨h1, h2⟩
  exact h ⟨h1, h2.imp_left (hR q hq)⟩

theorem tch_meet (hR : ∀ q, G q → R q → R' q) {Wd T T' : Set U64} {q : U64} (hq : G q) (hT : T' ⊆ T) :
    E2E.tch R' User Wd q T' ⊆ E2E.tch R User Wd q T := by
  by_cases h' : E2E.Racy R' User Wd q
  · have h := racy_meet hR hq h'
    have e1 : E2E.tch R' User Wd q T' = insert q T' := by unfold E2E.tch; exact if_pos h'
    have e2 : E2E.tch R User Wd q T = insert q T := by unfold E2E.tch; exact if_pos h
    rw [e1, e2]
    exact Set.insert_subset_insert hT
  · have e1 : E2E.tch R' User Wd q T' = T' := by unfold E2E.tch; exact if_neg h'
    rw [e1]
    exact hT.trans E2E.tch_sub

/-- **`Once` for `R` gives `Once` for `R'` along a run on `guard st G W`** (module docstring). -/
theorem once_meetG (hR : ∀ q, G q → R q → R' q) (p : SProg X) (hz : NoZero p) :
    ∀ (Wd T T' : Set U64) (s : S) (a : A) (r : X × S × A), interp (PathObl.guard st G W) ar p s a = ok r →
      Once st ar R User Wd T p s a → T' ⊆ T → Once st ar R' User Wd T' p s a := by
  induction p with
  | ret x => intros; simp only [Once]
  | err e => intros; simp only [Once]
  | rd q k ih =>
    intro Wd T T' s a r h ho hT
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    by_cases hq : G q
    · rw [guard_read hq] at hv
      simp only [Once] at ho ⊢
      refine ⟨fun hr hq' => ho.1 (racy_meet hR hq hr) (hT hq'), fun v' hv' => ?_⟩
      rw [hv] at hv'
      have e := ok_inj_ff hv'
      subst e
      exact ih _ (hz _) _ _ _ s a r hk (ho.2 _ hv) (tch_meet hR hq hT)
    · rw [guard_read_out hq] at hv; exact absurd hv fail_not_ok
  | rdp q k ih =>
    intro Wd T T' s a r h ho hT
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    by_cases hq : G q ∧ G (core.num.U64.wrapping_add q 8#u64)
    · rw [guard_read_pair hq.1 hq.2] at hv
      simp only [Once] at ho ⊢
      refine ⟨fun hr hq' => ho.1 (racy_meet hR hq.1 hr) (hT hq'),
        fun hr hq' => ho.2.1 (racy_meet hR hq.2 hr) (tch_meet hR hq.1 hT hq'), fun v' hv' => ?_⟩
      rw [hv] at hv'
      have e := ok_inj_ff hv'
      subst e
      exact ih _ (hz _) _ _ _ s a r hk (ho.2.2 _ hv) (tch_meet hR hq.2 (tch_meet hR hq.1 hT))
    · have : (PathObl.guard st G W).read_pair s q = fail .panic := by
        show (if G q ∧ G (core.num.U64.wrapping_add q 8#u64) then st.read_pair s q else fail .panic) = _
        rw [if_neg hq]
      rw [this] at hv; exact absurd hv fail_not_ok
  | wr q v k ih =>
    intro Wd T T' s a r h ho hT
    simp only [interp] at h
    obtain ⟨s', hv, hk⟩ := bok.mp h
    by_cases hq : W q
    · rw [guard_write hq] at hv
      simp only [Once] at ho ⊢
      intro s'' hs''
      rw [hv] at hs''
      have e := ok_inj_ff hs''
      subst e
      have h1 := ho s' hv
      by_cases hu : User q
      · simp only [if_pos hu] at h1 ⊢
        exact ih hz _ _ _ _ a r hk h1 (Set.insert_subset_insert hT)
      · simp only [if_neg hu] at h1 ⊢
        exact ih hz _ _ _ _ a r hk h1 hT
    · rw [guard_write_out hq] at hv; exact absurd hv fail_not_ok
  | zero q n k ih => exact absurd hz id
  | clr q n k ih => exact absurd hz id
  | ksb k ih =>
    intro Wd T T' s a r h ho hT
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv2 : st.ks_base s = ok v := hv
    simp only [Once] at ho ⊢
    intro v' hv'
    rw [hv2] at hv'
    have e := ok_inj_ff hv'
    subst e
    exact ih _ (hz _) _ _ _ s a r hk (ho _ hv2) hT
  | cpu k ih =>
    intro Wd T T' s a r h ho hT
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv2 : st.cur_cpu s = ok v := hv
    simp only [Once] at ho ⊢
    intro v' hv'
    rw [hv2] at hv'
    have e := ok_inj_ff hv'
    subst e
    exact ih _ (hz _) _ _ _ s a r hk (ho _ hv2) hT
  | masks k ih =>
    intro Wd T T' s a r h ho hT
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv2 : st.frame_masks s = ok v := hv
    simp only [Once] at ho ⊢
    intro v' hv'
    rw [hv2] at hv'
    have e := ok_inj_ff hv'
    subst e
    exact ih _ (hz _) _ _ _ s a r hk (ho _ hv2) hT
  | arch op k ih =>
    intro Wd T T' s a r h ho hT
    simp only [interp] at h
    obtain ⟨⟨v, a'⟩, hv, hk⟩ := bok.mp h
    simp only [Once] at ho ⊢
    intro v' a'' hv'
    rw [hv] at hv'
    obtain ⟨e1, e2⟩ := Prod.mk.inj (ok_inj_ff hv')
    subst e1
    subst e2
    exact ih _ (hz _) _ _ _ s _ r hk (ho _ _ hv) hT

end meet

end Fl4Proofs.P2.PathObl
