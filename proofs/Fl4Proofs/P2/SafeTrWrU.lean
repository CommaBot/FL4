/-
# P2 (line p3mc, gen 28): `safe_tr_wr` for a program that also reads user words

Handoff §32b. `PathObl.safe_tr_wr` asks the guarded run to read only an agreement set `Rd` holding no user word, and
derives `Once` from that (`once_of_guardG`). The truncated CNodeDelete's error reply reads (and rewrites) a word of
the caller's IPC buffer, a **user** word, whose value the translated program reads racily (`.rds`) with any value.

* **`once_downR`**: along a run on `guard st (R ∪ U) W` (`R` no user word, `U` only user words), `Once` for a read
  set `R'` gives `Once` for any `Ro` between `R` and `R'`: every read is of an `R` word (racy for neither) or of a
  `U` word (racy for both), so the two runs of `Once` track the same racy words.
* **`safe_tr_wrU`**: `safe_tr_wr` with the guard's read set `Rd ∪ Ru` (`Ru` aligned user words, any values in the
  state: the agreement with `ρ` is asked on `Rd` only) and `Once` for `Ro` supplied by the caller.

No named premises; no existing statement changed.
-/
import Fl4Proofs.P2.SafeTrWr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once Racy tch tr reads safe_tr_of_states exists_mem_state OwnDep MasksWr masksOf masksOf_eq)
open Fl4Proofs.P2.Serial (Owner ClsOwner HeldV PO Safe MoveHeld Adm)

noncomputable section
open Classical

section down
variable {S A X : Type} {st : machine.Store S} {ar : machine.Arch A}

theorem racy_eqRU {User R Ro R' U : U64 → Prop} (hRu : ∀ q, R q → ¬ User q) (hRo : ∀ q, R q → Ro q)
    (hRo' : ∀ q, Ro q → R' q) (hU : ∀ q, U q → User q) {Wd : Set U64} {q : U64} (hq : R q ∨ U q) :
    Racy Ro User Wd q = Racy R' User Wd q := by
  unfold Racy
  rcases hq with h | h
  · apply propext
    exact ⟨fun h1 _ => h1 ⟨hRu q h, Or.inl (hRo q h)⟩,
      fun h1 _ => h1 ⟨hRu q h, Or.inl (hRo' q (hRo q h))⟩⟩
  · apply propext
    exact ⟨fun _ hn => hn.1 (hU q h), fun _ hn => hn.1 (hU q h)⟩

theorem tch_eqRU {User R Ro R' U : U64 → Prop} (hRu : ∀ q, R q → ¬ User q) (hRo : ∀ q, R q → Ro q)
    (hRo' : ∀ q, Ro q → R' q) (hU : ∀ q, U q → User q) {Wd T : Set U64} {q : U64} (hq : R q ∨ U q) :
    tch Ro User Wd q T = tch R' User Wd q T := by
  unfold tch; rw [racy_eqRU hRu hRo hRo' hU hq]

/-- **`Once` for a smaller read set along a run reading only `R` and user words** (module docstring). -/
theorem once_downR {User R Ro R' U W : U64 → Prop} (hRu : ∀ q, R q → ¬ User q) (hRo : ∀ q, R q → Ro q)
    (hRo' : ∀ q, Ro q → R' q) (hU : ∀ q, U q → User q) (p : SProg X) (hz : NoZero p) :
    ∀ (Wd T : Set U64) (s : S) (a : A) (r : X × S × A),
      interp (PathObl.guard st (fun b => R b ∨ U b) W) ar p s a = ok r →
      Once st ar R' User Wd T p s a → Once st ar Ro User Wd T p s a := by
  induction p with
  | ret x => intro Wd T s a r _ _; simp only [Once]
  | err e => intro Wd T s a r h; exact absurd h fail_not_ok
  | rd q k ih =>
    intro Wd T s a r h hO
    simp only [interp] at h
    simp only [Once] at hO ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    by_cases hq : R q ∨ U q
    · rw [guard_read (R := fun b => R b ∨ U b) hq] at hv
      rw [racy_eqRU hRu hRo hRo' hU hq, tch_eqRU hRu hRo hRo' hU hq]
      refine ⟨hO.1, fun v' hv' => ?_⟩
      rw [hv] at hv'
      have e := ok_inj_ff hv'
      subst e
      exact ih _ (hz _) _ _ s a r hk (hO.2 _ hv)
    · rw [guard_read_out (R := fun b => R b ∨ U b) hq] at hv; exact absurd hv fail_not_ok
  | rdp q k ih =>
    intro Wd T s a r h hO
    simp only [interp] at h
    simp only [Once] at hO ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    by_cases hq : (R q ∨ U q) ∧ (R (core.num.U64.wrapping_add q 8#u64) ∨ U (core.num.U64.wrapping_add q 8#u64))
    · rw [guard_read_pair (R := fun b => R b ∨ U b) hq.1 hq.2] at hv
      rw [racy_eqRU hRu hRo hRo' hU hq.1, tch_eqRU hRu hRo hRo' hU hq.1, racy_eqRU hRu hRo hRo' hU hq.2,
        tch_eqRU hRu hRo hRo' hU hq.2]
      refine ⟨hO.1, hO.2.1, fun v' hv' => ?_⟩
      rw [hv] at hv'
      have e := ok_inj_ff hv'
      subst e
      exact ih _ (hz _) _ _ s a r hk (hO.2.2 _ hv)
    · have : (PathObl.guard st (fun b => R b ∨ U b) W).read_pair s q = fail .panic := by
        dsimp only [PathObl.guard]
        rw [if_neg hq]
      rw [this] at hv; exact absurd hv fail_not_ok
  | wr q v k ih =>
    intro Wd T s a r h hO
    simp only [interp] at h
    simp only [Once] at hO ⊢
    obtain ⟨s', hv, hk⟩ := bok.mp h
    by_cases hq : W q
    · rw [guard_write hq] at hv
      intro s'' hs''
      rw [hv] at hs''
      have e := ok_inj_ff hs''
      subst e
      exact ih hz _ _ _ a r hk (hO _ hv)
    · rw [guard_write_out hq] at hv; exact absurd hv fail_not_ok
  | zero q n k ih => exact absurd hz id
  | clr q n k ih => exact absurd hz id
  | ksb k ih =>
    intro Wd T s a r h hO
    simp only [interp] at h
    simp only [Once] at hO ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv2 : st.ks_base s = ok v := hv
    intro v' hv'
    rw [hv2] at hv'
    have e := ok_inj_ff hv'
    subst e
    exact ih _ (hz _) _ _ s a r hk (hO _ hv2)
  | cpu k ih =>
    intro Wd T s a r h hO
    simp only [interp] at h
    simp only [Once] at hO ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv2 : st.cur_cpu s = ok v := hv
    intro v' hv'
    rw [hv2] at hv'
    have e := ok_inj_ff hv'
    subst e
    exact ih _ (hz _) _ _ s a r hk (hO _ hv2)
  | masks k ih =>
    intro Wd T s a r h hO
    simp only [interp] at h
    simp only [Once] at hO ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv2 : st.frame_masks s = ok v := hv
    intro v' hv'
    rw [hv2] at hv'
    have e := ok_inj_ff hv'
    subst e
    exact ih _ (hz _) _ _ s a r hk (hO _ hv2)
  | arch op k ih =>
    intro Wd T s a r h hO
    simp only [interp] at h
    simp only [Once] at hO ⊢
    obtain ⟨⟨v, a'⟩, hv, hk⟩ := bok.mp h
    intro v' a'' hv'
    rw [hv] at hv'
    obtain ⟨e1, e2⟩ := Prod.mk.inj (ok_inj_ff hv')
    subst e1
    subst e2
    exact ih _ (hz _) _ _ s _ r hk (hO _ _ hv)

end down

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **A program writing held words and reading user words, run on a guard at every state carrying `ρ` on its
kernel reads, is `Safe`** (module docstring). -/
theorem safe_tr_wrU {X : Type} {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {kt : U64 → ClsOwner U64} {User : U64 → Prop} (hL : MoveHeld own) (hO : OwnDep own User) (hmk : MasksWr st)
    {c : U64} {hs : U64 → Prop} {μ ρ : U64 → U64} {σ : S} {a : A} (p : SProg X)
    (hc : L.cpu σ = c) {Ro Rd Ru Wd : U64 → Prop}
    (hal : ∀ b, Rd b → Aligned b) (hR0 : ∀ q, Rd q → Ro q ∧ ¬ User q) (hUa : ∀ b, Ru b → Aligned b)
    (hWd : ∀ x, Wd x → Aligned x ∧ (¬ User x → HeldV c hs (own μ x)))
    (hRPO : ∀ x, ¬ User x → Ro x → PO c hs (own μ x))
    (hρμ : ∀ x, PO c hs (own μ x) → ρ x = μ x)
    (hgo : ∀ s : S, L.cpu s = L.cpu σ → L.ksb s = L.ksb σ → (∀ b, Rd b → L.mem s b = ρ b) →
      ∃ r, interp (guard st (fun b => Rd b ∨ Ru b) Wd) ar p s a = ok r ∧
        WithinM st ar (fun x y => StepOK own cls kt User c hs (L.mem x) (L.mem y)) p s a ∧
        Once st ar Ro User ∅ ∅ p s a) :
    Safe own cls kt c hs μ (tr Ro User cls kt c (L.ksb σ) (masksOf st σ) ar p ∅ a) := by
  refine safe_tr_of_states hL hO hmk (Hp := fun x => Wd x ∧ ¬ User x) _ a
    (fun x hx => (hWd x hx.1).2 hx.2) hRPO ?_
  intro ν hν
  generalize hq : tr Ro User cls kt c (L.ksb σ) (masksOf st σ) ar p ∅ a = q
  obtain ⟨s, sc, sk, sm, hmem0⟩ := exists_mem_state hmk σ (fun x => if x ∈ reads q ν then ν x else ρ x)
  have hmem : ∀ x, Aligned x → L.mem s x = if x ∈ reads q ν then ν x else ρ x := hmem0
  have eR : ∀ b, Ro b → ¬ User b → (if b ∈ reads q ν then ν b else ρ b) = ρ b := by
    intro b hb hu'
    split_ifs
    · exact (hν.1 b (hRPO b hu' hb)).trans (hρμ b (hRPO b hu' hb)).symm
    · rfl
  have hag : ∀ b, Rd b → L.mem s b = ρ b := fun b hb => by
    rw [hmem b (hal b hb), eR b (hR0 b hb).1 (hR0 b hb).2]
  obtain ⟨r, hg, hWM, hOnce⟩ := hgo s sc sk hag
  have hW := (interp_guard _ s a r hg).2
  refine ⟨s, Wd, sc.trans hc, sk, sm.trans (masksOf_eq st σ),
    Within.mono (fun b hb => hb.elim (hal b) (hUa b)) (fun b hb => hb) _ s a hW, hWM, hOnce,
    fun x hx => ⟨(hWd x hx).1, fun hu => ⟨hx, hu⟩⟩, fun x hx hxa => by rw [hmem x hxa, if_pos hx],
    fun x hxa hu' hne hpo => hne ?_⟩
  rw [hmem x hxa]
  split_ifs
  · exact hν.1 x hpo
  · exact hρμ x hpo

end

end
end Fl4Proofs.P2.PathObl
