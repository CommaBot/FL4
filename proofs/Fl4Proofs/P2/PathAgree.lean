/-
# P2: a guarded run of a tree transfers to agreeing states and to other checking stores

For a tree `p` of trait calls without `zero` / `clear_free` (`PathObl.NoZero`):

* `interp_to`: a successful run on `guard st R W` is the same run on any store that answers the reads in `R` and
  the writes in `W` as `st` does (a larger guard, or `mguard st Q` when every write in `W` passes `Q`);
* `interp_agree`: a successful run on `guard st R W` from `s` gives, from every state that agrees with `s` on `R`
  (and on the kernel base, the core and the frame masks), a successful run on `guard st R W` with the same answer
  and the same Arch value.

With `PathObl.IsProg` these turn one guarded run at the entry state (`acc`, or a decline whose reads are all in
`ReadSet`) into `dec_alt` / `PathSide.read_aligned` at every alternative.

Premise: `hm` [P], writes leave `frame_masks` alone (p2c's `P2/E2E`).
-/
import Fl4Proofs.P2.PathBridge
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Classical

section
variable {S A X : Type} {st : machine.Store S} {ar : machine.Arch A} {R W : U64 → Prop}

theorem interp_to {st' : machine.Store S} (hr : ∀ s q, R q → st'.read s q = st.read s q)
    (hp : ∀ s q, R q → R (core.num.U64.wrapping_add q 8#u64) → st'.read_pair s q = st.read_pair s q)
    (hw : ∀ s q v, W q → st'.write s q v = st.write s q v)
    (h1 : st'.ks_base = st.ks_base) (h2 : st'.cur_cpu = st.cur_cpu) (h3 : st'.frame_masks = st.frame_masks)
    (p : SProg X) (hz : NoZero p) :
    ∀ (s : S) (a : A) (r : X × S × A), interp (guard st R W) ar p s a = ok r → interp st' ar p s a = ok r := by
  induction p with
  | ret x => intro s a r h; exact h
  | err e => intro s a r h; exact absurd h fail_not_ok
  | rd q k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    by_cases hq : R q
    · rw [guard_read hq] at hv
      exact bok.mpr ⟨v, by rw [hr s q hq]; exact hv, ih v (hz v) s a r hk⟩
    · rw [guard_read_out hq] at hv; exact absurd hv fail_not_ok
  | rdp q k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    by_cases hq : R q ∧ R (core.num.U64.wrapping_add q 8#u64)
    · rw [guard_read_pair hq.1 hq.2] at hv
      exact bok.mpr ⟨v, by rw [hp s q hq.1 hq.2]; exact hv, ih v (hz v) s a r hk⟩
    · have : (guard st R W).read_pair s q = fail .panic := by
        show (if R q ∧ R (core.num.U64.wrapping_add q 8#u64) then st.read_pair s q else fail .panic) = _
        rw [if_neg hq]
      rw [this] at hv; exact absurd hv fail_not_ok
  | wr q v k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨s', hv, hk⟩ := bok.mp h
    by_cases hq : W q
    · rw [guard_write hq] at hv
      exact bok.mpr ⟨s', by rw [hw s q v hq]; exact hv, ih hz s' a r hk⟩
    · rw [guard_write_out hq] at hv; exact absurd hv fail_not_ok
  | zero q n k ih => exact absurd hz id
  | clr q n k ih => exact absurd hz id
  | ksb k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, by rw [h1]; exact hv, ih v (hz v) s a r hk⟩
  | cpu k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, by rw [h2]; exact hv, ih v (hz v) s a r hk⟩
  | masks k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, by rw [h3]; exact hv, ih v (hz v) s a r hk⟩
  | arch op k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨⟨v, a'⟩, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨(v, a'), hv, ih v (hz v) s a' r hk⟩

/-- A guarded run passes a larger guard. -/
theorem interp_mono {R' W' : U64 → Prop} (hR : ∀ q, R q → R' q) (hW : ∀ q, W q → W' q) (p : SProg X) (hz : NoZero p)
    (s : S) (a : A) (r : X × S × A) (h : interp (guard st R W) ar p s a = ok r) :
    interp (guard st R' W') ar p s a = ok r :=
  interp_to (fun _ q hq => guard_read (hR q hq)) (fun _ q h1 h2 => guard_read_pair (hR q h1) (hR _ h2))
    (fun _ q _ hq => guard_write (hW q hq)) rfl rfl rfl p hz s a r h

/-- A guarded run whose admitted writes all pass `Q` passes the checking store. -/
theorem interp_to_mguard [L : LawfulStore st] {Q : S → S → Prop} (hQ : ∀ s q v, W q → Q s (L.wr s q v)) (p : SProg X)
    (hz : NoZero p) (s : S) (a : A) (r : X × S × A) (h : interp (guard st R W) ar p s a = ok r) :
    interp (mguard st Q) ar p s a = ok r :=
  interp_to (st := st) (st' := mguard st Q) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun s q v hq => by
      show (do let s' ← st.write s q v
               if Q s s' then ok s' else fail .panic) = _
      rw [L.write_eq, bind_tc_ok, if_pos (hQ s q v hq)]) rfl rfl rfl p hz s a r h

/-- **Agreement**: see the module docstring. -/
theorem interp_agree [L : LawfulStore st] (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hRal : ∀ w, R w → Aligned w) (hWal : ∀ w, W w → Aligned w) (p : SProg X) (hz : NoZero p) :
    ∀ (s s' : S) (a : A) (x : X) (s1 : S) (a1 : A), L.ksb s' = L.ksb s → L.cpu s' = L.cpu s →
      st.frame_masks s' = st.frame_masks s → (∀ w, R w → L.mem s' w = L.mem s w) →
      interp (guard st R W) ar p s a = ok (x, s1, a1) →
      ∃ s1', interp (guard st R W) ar p s' a = ok (x, s1', a1) := by
  induction p with
  | ret x =>
    intro s s' a y s1 a1 _ _ _ _ h
    simp only [interp] at h ⊢
    obtain ⟨rfl, -, rfl⟩ := by simpa using Result.ok_injective h
    exact ⟨s', rfl⟩
  | err e => intro s s' a y s1 a1 _ _ _ _ h; exact absurd h fail_not_ok
  | rd q k ih =>
    intro s s' a y s1 a1 e1 e2 e3 e4 h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    by_cases hq : R q
    · rw [guard_read hq, L.read_eq, ← e4 q hq, ← L.read_eq] at hv
      obtain ⟨s1', h'⟩ := ih v (hz v) s s' a y s1 a1 e1 e2 e3 e4 hk
      exact ⟨s1', bok.mpr ⟨v, by rw [guard_read hq]; exact hv, h'⟩⟩
    · rw [guard_read_out hq] at hv; exact absurd hv fail_not_ok
  | rdp q k ih =>
    intro s s' a y s1 a1 e1 e2 e3 e4 h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    by_cases hq : R q ∧ R (core.num.U64.wrapping_add q 8#u64)
    · rw [guard_read_pair hq.1 hq.2, L.read_pair_eq, ← e4 q hq.1, ← e4 _ hq.2, ← L.read_pair_eq] at hv
      obtain ⟨s1', h'⟩ := ih v (hz v) s s' a y s1 a1 e1 e2 e3 e4 hk
      exact ⟨s1', bok.mpr ⟨v, by rw [guard_read_pair hq.1 hq.2]; exact hv, h'⟩⟩
    · have : (guard st R W).read_pair s q = fail .panic := by
        show (if R q ∧ R (core.num.U64.wrapping_add q 8#u64) then st.read_pair s q else fail .panic) = _
        rw [if_neg hq]
      rw [this] at hv; exact absurd hv fail_not_ok
  | wr q v k ih =>
    intro s s' a y s1 a1 e1 e2 e3 e4 h
    simp only [interp] at h ⊢
    obtain ⟨s2, hv, hk⟩ := bok.mp h
    by_cases hq : W q
    · rw [guard_write hq, L.write_eq] at hv
      obtain rfl := Result.ok_injective hv
      obtain ⟨s1', h'⟩ := ih hz (L.wr s q v) (L.wr s' q v) a y s1 a1 (by rw [L.ksb_wr, L.ksb_wr, e1])
        (by rw [L.cpu_wr, L.cpu_wr, e2]) (by rw [hm, hm, e3])
        (fun w hw => by
          rw [L.mem_wr _ _ _ _ (hWal q hq) (hRal w hw), L.mem_wr _ _ _ _ (hWal q hq) (hRal w hw), e4 w hw]) hk
      exact ⟨s1', bok.mpr ⟨L.wr s' q v, by rw [guard_write hq, L.write_eq], h'⟩⟩
    · rw [guard_write_out hq] at hv; exact absurd hv fail_not_ok
  | zero q n k ih => exact absurd hz id
  | clr q n k ih => exact absurd hz id
  | ksb k ih =>
    intro s s' a y s1 a1 e1 e2 e3 e4 h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    obtain ⟨s1', h'⟩ := ih v (hz v) s s' a y s1 a1 e1 e2 e3 e4 hk
    refine ⟨s1', bok.mpr ⟨v, ?_, h'⟩⟩
    show st.ks_base s' = ok v
    have : st.ks_base s = ok v := hv
    rw [L.ks_base_eq] at this ⊢; rw [e1]; exact this
  | cpu k ih =>
    intro s s' a y s1 a1 e1 e2 e3 e4 h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    obtain ⟨s1', h'⟩ := ih v (hz v) s s' a y s1 a1 e1 e2 e3 e4 hk
    refine ⟨s1', bok.mpr ⟨v, ?_, h'⟩⟩
    show st.cur_cpu s' = ok v
    have : st.cur_cpu s = ok v := hv
    rw [L.cur_cpu_eq] at this ⊢; rw [e2]; exact this
  | masks k ih =>
    intro s s' a y s1 a1 e1 e2 e3 e4 h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    obtain ⟨s1', h'⟩ := ih v (hz v) s s' a y s1 a1 e1 e2 e3 e4 hk
    refine ⟨s1', bok.mpr ⟨v, ?_, h'⟩⟩
    show st.frame_masks s' = ok v
    rw [e3]; exact hv
  | arch op k ih =>
    intro s s' a y s1 a1 e1 e2 e3 e4 h
    simp only [interp] at h ⊢
    obtain ⟨⟨v, a'⟩, hv, hk⟩ := bok.mp h
    obtain ⟨s1', h'⟩ := ih v (hz v) s s' a' y s1 a1 e1 e2 e3 e4 hk
    exact ⟨s1', bok.mpr ⟨(v, a'), hv, h'⟩⟩

end

end Fl4Proofs.P2.PathObl
