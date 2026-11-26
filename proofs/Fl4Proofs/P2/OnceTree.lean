/-
# P2: `E2E.Once` along a concrete tree, piece by piece (line hpzg)

With the local paths' trees now concrete (`P2/ProgGen*.lean`), `ReadOnce` can be shown by walking the tree:
a guarded prefix makes no racy read and leaves the touched set `T` as it was, so `Once` of `p.sbind f` reduces
to `Once` of the continuation; at the one racy read, `Once` asks only that the word was not touched before.

* `racy_mono` / `tch_mono` / `once_mono`: `Once` is monotone (more written kernel words `Wd`, fewer touched
  words `T`);
* `once_sbind_guard`: if `p` runs on `PathObl.guard st R0 W0` (`R0` inside `R`, `R0` / `W0` without user
  words), `Once` of `p.sbind f` follows from `Once` of `f` at `p`'s result, for every larger `Wd`;
* `once_rd_first`: a read of a word not yet touched, then a guarded run: `Once`.

No premises.
-/
import Fl4Proofs.P2.OnceGuard
import Fl4Proofs.P2.ProgReify
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.E2E (Once)

section
open Classical
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} {R User : U64 → Prop}

theorem racy_mono {Wd Wd' : Set U64} {q : U64} (hW : Wd ⊆ Wd') (h : E2E.Racy R User Wd' q) :
    E2E.Racy R User Wd q := by
  unfold E2E.Racy at *
  rintro ⟨h1, h2⟩
  exact h ⟨h1, h2.imp_right (fun x => hW x)⟩

theorem tch_mono {Wd Wd' T T' : Set U64} {q : U64} (hW : Wd ⊆ Wd') (hT : T' ⊆ T) :
    E2E.tch R User Wd' q T' ⊆ E2E.tch R User Wd q T := by
  by_cases h' : E2E.Racy R User Wd' q
  · have h := racy_mono hW h'
    have e1 : E2E.tch R User Wd' q T' = insert q T' := by unfold E2E.tch; exact if_pos h'
    have e2 : E2E.tch R User Wd q T = insert q T := by unfold E2E.tch; exact if_pos h
    rw [e1, e2]
    exact Set.insert_subset_insert hT
  · have e1 : E2E.tch R User Wd' q T' = T' := by unfold E2E.tch; exact if_neg h'
    rw [e1]
    exact hT.trans E2E.tch_sub

/-- **`Once` is monotone**: more written words, fewer touched words. -/
theorem once_mono {X : Type} (p : SProg X) : ∀ (Wd T Wd' T' : Set U64) (s : S) (a : A),
    Once st ar R User Wd T p s a → Wd ⊆ Wd' → T' ⊆ T → Once st ar R User Wd' T' p s a := by
  induction p with
  | ret x => intros; simp only [Once]
  | err e => intros; simp only [Once]
  | rd q k ih =>
    intro Wd T Wd' T' s a h hW hT
    simp only [Once] at h ⊢
    exact ⟨fun hr hq => h.1 (racy_mono hW hr) (hT hq),
      fun v hv => ih v _ _ _ _ s a (h.2 v hv) hW (tch_mono hW hT)⟩
  | rdp q k ih =>
    intro Wd T Wd' T' s a h hW hT
    simp only [Once] at h ⊢
    exact ⟨fun hr hq => h.1 (racy_mono hW hr) (hT hq),
      fun hr hq => h.2.1 (racy_mono hW hr) (tch_mono hW hT hq),
      fun v hv => ih v _ _ _ _ s a (h.2.2 v hv) hW (tch_mono hW (tch_mono hW hT))⟩
  | wr q v k ih =>
    intro Wd T Wd' T' s a h hW hT
    simp only [Once] at h ⊢
    intro s' hs'
    have h1 := h s' hs'
    by_cases hu : User q
    · simp only [if_pos hu] at h1 ⊢
      exact ih _ _ _ _ s' a h1 hW (Set.insert_subset_insert hT)
    · simp only [if_neg hu] at h1 ⊢
      exact ih _ _ _ _ s' a h1 (Set.insert_subset_insert hW) hT
  | zero q n k ih => intro Wd T Wd' T' s a h; simp only [Once] at h
  | clr q n k ih => intro Wd T Wd' T' s a h; simp only [Once] at h
  | ksb k ih =>
    intro Wd T Wd' T' s a h hW hT
    simp only [Once] at h ⊢
    exact fun v hv => ih v _ _ _ _ s a (h v hv) hW hT
  | cpu k ih =>
    intro Wd T Wd' T' s a h hW hT
    simp only [Once] at h ⊢
    exact fun v hv => ih v _ _ _ _ s a (h v hv) hW hT
  | masks k ih =>
    intro Wd T Wd' T' s a h hW hT
    simp only [Once] at h ⊢
    exact fun v hv => ih v _ _ _ _ s a (h v hv) hW hT
  | arch op k ih =>
    intro Wd T Wd' T' s a h hW hT
    simp only [Once] at h ⊢
    exact fun v a' hv => ih v _ _ _ _ s a' (h v a' hv) hW hT

/-- **A guarded prefix makes no racy read**: `Once` of `p.sbind f` from `Once` of `f` at `p`'s result (for every
larger `Wd`, the prefix's kernel writes). -/
theorem once_sbind_guard {X Y : Type} {R0 W0 : U64 → Prop} (hR0 : ∀ q, R0 q → R q ∧ ¬ User q)
    (hW0 : ∀ q, W0 q → ¬ User q) (p : SProg X) (hz : NoZero p) (f : X → SProg Y) :
    ∀ (Wd T : Set U64) (s : S) (a : A) (r : X × S × A), interp (guard st R0 W0) ar p s a = ok r →
      (∀ Wd', Wd ⊆ Wd' → Once st ar R User Wd' T (f r.1) r.2.1 r.2.2) →
      Once st ar R User Wd T (p.sbind f) s a := by
  induction p with
  | ret x =>
    intro Wd T s a r h hf
    rw [interp_ret'] at h
    have e := ok_inj_ff h
    subst e
    exact hf Wd subset_rfl
  | err e => intro Wd T s a r h; exact absurd h fail_not_ok
  | rd q k ih =>
    intro Wd T s a r h hf
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    by_cases hq : R0 q
    · rw [guard_read hq] at hv
      have nr : ¬ E2E.Racy R User Wd q := fun hr =>
        hr ⟨(hR0 q hq).2, Or.inl (hR0 q hq).1⟩
      simp only [SProg.sbind, Once]
      refine ⟨fun hr => absurd hr nr, fun v' hv' => ?_⟩
      rw [hv] at hv'
      have e := ok_inj_ff hv'
      subst e
      have et : E2E.tch R User Wd q T = T := by unfold E2E.tch; exact if_neg nr
      rw [et]
      exact ih _ (hz _) Wd T s a r hk hf
    · rw [guard_read_out hq] at hv; exact absurd hv fail_not_ok
  | rdp q k ih =>
    intro Wd T s a r h hf
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    by_cases hq : R0 q ∧ R0 (core.num.U64.wrapping_add q 8#u64)
    · rw [guard_read_pair hq.1 hq.2] at hv
      have nr1 : ¬ E2E.Racy R User Wd q := fun hr =>
        hr ⟨(hR0 q hq.1).2, Or.inl (hR0 q hq.1).1⟩
      have nr2 : ¬ E2E.Racy R User Wd (core.num.U64.wrapping_add q 8#u64) := fun hr =>
        hr ⟨(hR0 _ hq.2).2, Or.inl (hR0 _ hq.2).1⟩
      simp only [SProg.sbind, Once]
      have et1 : E2E.tch R User Wd q T = T := by unfold E2E.tch; exact if_neg nr1
      have et2 : E2E.tch R User Wd (core.num.U64.wrapping_add q 8#u64) T = T := by
        unfold E2E.tch; exact if_neg nr2
      refine ⟨fun hr => absurd hr nr1, fun hr => absurd hr nr2, fun v' hv' => ?_⟩
      rw [hv] at hv'
      have e := ok_inj_ff hv'
      subst e
      rw [et1, et2]
      exact ih _ (hz _) Wd T s a r hk hf
    · have : (PathObl.guard st R0 W0).read_pair s q = fail .panic := by
        show (if R0 q ∧ R0 (core.num.U64.wrapping_add q 8#u64) then st.read_pair s q else fail .panic) = _
        rw [if_neg hq]
      rw [this] at hv; exact absurd hv fail_not_ok
  | wr q v k ih =>
    intro Wd T s a r h hf
    simp only [interp] at h
    obtain ⟨s', hv, hk⟩ := bok.mp h
    by_cases hq : W0 q
    · rw [guard_write hq] at hv
      simp only [SProg.sbind, Once]
      intro s'' hs''
      rw [hv] at hs''
      have e := ok_inj_ff hs''
      subst e
      simp only [if_neg (hW0 q hq)]
      exact ih hz (insert q Wd) T s' a r hk
        (fun Wd' hW' => hf Wd' ((Set.subset_insert _ _).trans hW'))
    · rw [guard_write_out hq] at hv; exact absurd hv fail_not_ok
  | zero q n k ih => exact absurd hz id
  | clr q n k ih => exact absurd hz id
  | ksb k ih =>
    intro Wd T s a r h hf
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv2 : st.ks_base s = ok v := hv
    simp only [SProg.sbind, Once]
    intro v' hv'
    rw [hv2] at hv'
    have e := ok_inj_ff hv'
    subst e
    exact ih _ (hz _) Wd T s a r hk hf
  | cpu k ih =>
    intro Wd T s a r h hf
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv2 : st.cur_cpu s = ok v := hv
    simp only [SProg.sbind, Once]
    intro v' hv'
    rw [hv2] at hv'
    have e := ok_inj_ff hv'
    subst e
    exact ih _ (hz _) Wd T s a r hk hf
  | masks k ih =>
    intro Wd T s a r h hf
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv2 : st.frame_masks s = ok v := hv
    simp only [SProg.sbind, Once]
    intro v' hv'
    rw [hv2] at hv'
    have e := ok_inj_ff hv'
    subst e
    exact ih _ (hz _) Wd T s a r hk hf
  | arch op k ih =>
    intro Wd T s a r h hf
    simp only [interp] at h
    obtain ⟨⟨v, a'⟩, hv, hk⟩ := bok.mp h
    simp only [SProg.sbind, Once]
    intro v' a'' hv'
    rw [hv] at hv'
    obtain ⟨e1, e2⟩ := Prod.mk.inj (ok_inj_ff hv')
    subst e1
    subst e2
    exact ih _ (hz _) Wd T s _ r hk hf

theorem SProg.sbind_ret {X : Type} (p : SProg X) : p.sbind SProg.ret = p := by
  induction p with
  | ret x => rfl
  | err e => rfl
  | rd q k ih => simp only [SProg.sbind, ih]
  | rdp q k ih => simp only [SProg.sbind, ih]
  | wr q v k ih => simp only [SProg.sbind, ih]
  | zero q n k ih => simp only [SProg.sbind, ih]
  | clr q n k ih => simp only [SProg.sbind, ih]
  | ksb k ih => simp only [SProg.sbind, ih]
  | cpu k ih => simp only [SProg.sbind, ih]
  | masks k ih => simp only [SProg.sbind, ih]
  | arch op k ih => simp only [SProg.sbind, ih]

/-- **A guarded run is `Once`** for any `R` holding the guard's read set (`once_of_guardG` with `R0 ⊆ R`). -/
theorem once_of_guardR {X : Type} {R0 W0 : U64 → Prop} (hR0 : ∀ q, R0 q → R q ∧ ¬ User q)
    (hW0 : ∀ q, W0 q → ¬ User q) (p : SProg X) (hz : NoZero p) (Wd T : Set U64) (s : S) (a : A)
    (r : X × S × A) (h : interp (guard st R0 W0) ar p s a = ok r) : Once st ar R User Wd T p s a := by
  have := once_sbind_guard (st := st) (User := User) hR0 hW0 p hz SProg.ret Wd T s a r h
    (fun _ _ => by simp only [Once])
  rwa [SProg.sbind_ret] at this

/-- **A first read, then a guarded run**: reading a word not touched before, then running on
`guard st R0 W0` (`R0` inside `R`, `R0` / `W0` without user words), is `Once`. -/
theorem once_rd_first {X : Type} {R0 W0 : U64 → Prop} (hR0 : ∀ q, R0 q → R q ∧ ¬ User q)
    (hW0 : ∀ q, W0 q → ¬ User q)
    (q : U64) (k : U64 → SProg X) (hz : ∀ v, NoZero (k v)) (Wd T : Set U64) (s : S) (a : A)
    (hq : q ∉ T) (hk : ∀ v, st.read s q = ok v → ∃ r, interp (guard st R0 W0) ar (k v) s a = ok r) :
    Once st ar R User Wd T (SProg.rd q k) s a := by
  simp only [Once]
  refine ⟨fun _ => hq, fun v hv => ?_⟩
  obtain ⟨r, hr⟩ := hk v hv
  exact once_of_guardR hR0 hW0 _ (hz v) _ _ s a r hr

theorem SProg.sbind_assoc {X Y Z : Type} (p : SProg X) (f : X → SProg Y) (g : Y → SProg Z) :
    (p.sbind f).sbind g = p.sbind (fun x => (f x).sbind g) := by
  induction p with
  | ret x => rfl
  | err e => rfl
  | rd q k ih => simp only [SProg.sbind, ih]
  | rdp q k ih => simp only [SProg.sbind, ih]
  | wr q v k ih => simp only [SProg.sbind, ih]
  | zero q n k ih => simp only [SProg.sbind, ih]
  | clr q n k ih => simp only [SProg.sbind, ih]
  | ksb k ih => simp only [SProg.sbind, ih]
  | cpu k ih => simp only [SProg.sbind, ih]
  | masks k ih => simp only [SProg.sbind, ih]
  | arch op k ih => simp only [SProg.sbind, ih]

/-- A pure step's run does not depend on the store. -/
theorem interp_liftR_store {X : Type} (m1 m2 : machine.Store S) (r : Result X) (s : S) (a : A) :
    interp m1 ar (SProg.liftR r) s a = interp m2 ar (SProg.liftR r) s a := by
  unfold SProg.liftR
  split_ifs <;> simp only [interp_ret', interp_err']

/-- **One step of a walk**: a guarded first part (its run on `st` is its run on the guard), then the rest. -/
theorem once_step {X Y : Type} {R0 W0 : U64 → Prop} (hR0 : ∀ q, R0 q → R q ∧ ¬ User q)
    (hW0 : ∀ q, W0 q → ¬ User q) {q : SProg X} (hz : NoZero q) {f : X → SProg Y} {Wd T : Set U64}
    {s : S} {a : A} {r' : Y × S × A} (h : interp st ar (q.sbind f) s a = ok r')
    (hg : ∀ r, interp st ar q s a = ok r → interp (guard st R0 W0) ar q s a = ok r)
    (hk : ∀ r, interp st ar q s a = ok r → interp st ar (f r.1) r.2.1 r.2.2 = ok r' →
      ∀ Wd', Wd ⊆ Wd' → Once st ar R User Wd' T (f r.1) r.2.1 r.2.2) :
    Once st ar R User Wd T (q.sbind f) s a := by
  rw [interp_sbind] at h
  obtain ⟨r, h1, h2⟩ := bind_eq_ok' h
  exact once_sbind_guard hR0 hW0 q hz f Wd T s a r (hg r h1) (hk r h1 h2)

end

end Fl4Proofs.P2.PathObl
