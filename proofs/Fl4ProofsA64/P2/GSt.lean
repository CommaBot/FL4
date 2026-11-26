-- AArch64 port of Fl4Proofs.P2.GSt (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
# P2: stores that answer as `st` on given words (`GRd`, `GWr`), and the checked store `gd`

`GRd g st R`: the store `g` answers reads of `R` words as `st`; `GWr g st W`:
writes of `W` words (any value, any state) as `st`; both: `ks_base`, `cur_cpu`
and `frame_masks` (`GK`) as `st`. The leaf lemmas `<f>.guard` (`AccessLeaf.lean` and the
`Access*.lean` files above it) are stated for any such `g`: they serve both

* `guard st R W` (`PathObl.acc`), and
* `gd st R P` (`PathObl.move`): writes checked by state, address **and value**,
  `P s a v`; `zero` / `clear_free` fail. `W` is then `WAll P`, the words any
  state may write with any value. A write whose value matters (a thread's
  `STATE`) is a leaf hypothesis of its own, `g.write X a v = st.write X a v`.

`interp_gd` (for a body's tree, `IsProg` [P]): a successful run on `gd st R P`
is the real run, and it is a run on `mguard st Q` whenever `P`, under an
invariant `I` its writes keep, gives `Q`.
-/
import Fl4ProofsA64.P2.PathBridge
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P2.PathObl
open fl4_core_a64 Fl4ProofsA64.P1

noncomputable section
open Classical

variable {S : Type}

/-- `g`'s constants (`ks_base`, `cur_cpu`, `frame_masks`) are `st`'s. -/
class GK (g : machine.Store S) (st : outParam (machine.Store S)) : Prop where
  ks_base : g.ks_base = st.ks_base
  cur_cpu : g.cur_cpu = st.cur_cpu
  frame_masks : g.frame_masks = st.frame_masks

/-- `g` answers reads of `R` words as `st`. -/
class GRd (g : machine.Store S) (st : outParam (machine.Store S)) (R : outParam (U64 → Prop)) : Prop
    extends GK g st where
  read : ∀ {a}, R a → ∀ s, g.read s a = st.read s a
  read_pair : ∀ {a}, R a → R (core.num.U64.wrapping_add a 8#u64) → ∀ s, g.read_pair s a = st.read_pair s a

/-- `g` answers writes of `W` words as `st`. -/
class GWr (g : machine.Store S) (st : outParam (machine.Store S)) (W : outParam (U64 → Prop)) : Prop
    extends GK g st where
  write : ∀ {a}, W a → ∀ s v, g.write s a v = st.write s a v

instance GRd.guard (st : machine.Store S) (R W : U64 → Prop) : GRd (PathObl.guard st R W) st R where
  read h _ := guard_read h
  read_pair h h8 _ := guard_read_pair h h8
  ks_base := rfl
  cur_cpu := rfl
  frame_masks := rfl

instance GWr.guard (st : machine.Store S) (R W : U64 → Prop) : GWr (PathObl.guard st R W) st W where
  write h _ _ := guard_write h
  ks_base := rfl
  cur_cpu := rfl
  frame_masks := rfl

section
variable {g st : machine.Store S} {R W : U64 → Prop}

theorem gst_read [G : GRd g st R] {s : S} {a : U64} (h : R a) : g.read s a = st.read s a := G.read h s

theorem gst_read_pair [G : GRd g st R] {s : S} {a : U64} (h : R a) (h8 : R (core.num.U64.wrapping_add a 8#u64)) :
    g.read_pair s a = st.read_pair s a := G.read_pair h h8 s

theorem gst_write [G : GWr g st W] {s : S} {a v : U64} (h : W a) : g.write s a v = st.write s a v := G.write h s v

theorem gst_ks_base [G : GK g st] : g.ks_base = st.ks_base := G.ks_base
theorem gst_cur_cpu [G : GK g st] : g.cur_cpu = st.cur_cpu := G.cur_cpu
theorem gst_frame_masks [G : GK g st] : g.frame_masks = st.frame_masks := G.frame_masks

end

/-! ## The store that checks writes by state, address and value -/

/-- Reads in `R`, writes allowed by `P` (state, address, value); no `zero` /
`clear_free`. -/
def gd (st : machine.Store S) (R : U64 → Prop) (P : S → U64 → U64 → Prop) : machine.Store S where
  frame_masks := st.frame_masks
  read s a := if R a then st.read s a else fail .panic
  read_pair s a :=
    if R a ∧ R (core.num.U64.wrapping_add a 8#u64) then st.read_pair s a else fail .panic
  write s a v := if P s a v then st.write s a v else fail .panic
  zero _ _ _ := fail .panic
  clear_free _ _ _ := fail .panic
  ks_base := st.ks_base
  cur_cpu := st.cur_cpu
  fetch_and _ _ _ := fail .panic

/-- `gd` narrows `st` (`PathBridge.Narrow`). -/
theorem Narrow.gd (st : machine.Store S) (R : U64 → Prop) (P : S → U64 → U64 → Prop) :
    PathObl.Narrow st (gd st R P) :=
  ⟨rfl, rfl, rfl, fun _ _ => PathObl.Nar.ite', fun _ _ => PathObl.Nar.ite', fun _ _ _ => PathObl.Nar.ite',
    fun _ _ _ => PathObl.Nar.fail' _ _, fun _ _ _ => PathObl.Nar.fail' _ _⟩

/-- The words `P` lets any state write with any value. -/
def WAll (P : S → U64 → U64 → Prop) (a : U64) : Prop := ∀ s v, P s a v

theorem gd_write {st : machine.Store S} {R : U64 → Prop} {P : S → U64 → U64 → Prop} {s : S} {a v : U64}
    (h : P s a v) : (gd st R P).write s a v = st.write s a v := by
  show (if P s a v then st.write s a v else fail .panic) = _
  rw [if_pos h]

instance GRd.gd (st : machine.Store S) (R : U64 → Prop) (P : S → U64 → U64 → Prop) :
    GRd (PathObl.gd st R P) st R where
  read {a} h s := by
    show (if R a then st.read s a else fail .panic) = _
    rw [if_pos h]
  read_pair {a} h h8 s := by
    show (if R a ∧ R (core.num.U64.wrapping_add a 8#u64) then st.read_pair s a else fail .panic) = _
    rw [if_pos ⟨h, h8⟩]
  ks_base := rfl
  cur_cpu := rfl
  frame_masks := rfl

instance GWr.gd (st : machine.Store S) (R : U64 → Prop) (P : S → U64 → U64 → Prop) :
    GWr (PathObl.gd st R P) st (WAll P) where
  write h s v := gd_write (h s v)
  ks_base := rfl
  cur_cpu := rfl
  frame_masks := rfl

variable {A X : Type}

/-- **From the checked store to `mguard`**: a run on `gd st R P` is a run on
`mguard st Q`, when every write `P` allows satisfies `Q` and keeps the
invariant `I`. -/
theorem interp_gd {st : machine.Store S} {ar : machine.Arch A} {R : U64 → Prop}
    {P : S → U64 → U64 → Prop} {Q : S → S → Prop} {I : S → Prop}
    (hP : ∀ s a v s', I s → P s a v → st.write s a v = ok s' → Q s s' ∧ I s') (p : SProg X) :
    ∀ (s : S) (a : A) (r : X × S × A), I s → interp (gd st R P) ar p s a = ok r →
      interp (mguard st Q) ar p s a = ok r := by
  induction p with
  | ret x => intro s a r _ h; exact h
  | err e => intro s a r _ h; exact h
  | rd q k ih =>
    intro s a r hI h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv' : (if R q then st.read s q else fail .panic) = ok v := hv
    by_cases hq : R q
    · rw [if_pos hq] at hv'
      exact bok.mpr ⟨v, hv', ih v s a r hI hk⟩
    · rw [if_neg hq] at hv'; exact absurd hv' fail_not_ok
  | rdp q k ih =>
    intro s a r hI h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv' : (if R q ∧ R (core.num.U64.wrapping_add q 8#u64) then st.read_pair s q else fail .panic) = ok v := hv
    by_cases hq : R q ∧ R (core.num.U64.wrapping_add q 8#u64)
    · rw [if_pos hq] at hv'
      exact bok.mpr ⟨v, hv', ih v s a r hI hk⟩
    · rw [if_neg hq] at hv'; exact absurd hv' fail_not_ok
  | wr q v k ih =>
    intro s a r hI h
    simp only [interp] at h ⊢
    obtain ⟨s', hv, hk⟩ := bok.mp h
    have hv' : (if P s q v then st.write s q v else fail .panic) = ok s' := hv
    by_cases hq : P s q v
    · rw [if_pos hq] at hv'
      obtain ⟨h1, h2⟩ := hP s q v s' hI hq hv'
      exact bok.mpr ⟨s', mguard_write hv' h1, ih s' a r h2 hk⟩
    · rw [if_neg hq] at hv'; exact absurd hv' fail_not_ok
  | zero q n k ih =>
    intro s a r hI h
    simp only [interp] at h
    obtain ⟨s', hv, _⟩ := bok.mp h
    exact absurd hv fail_not_ok
  | clr q n k ih =>
    intro s a r hI h
    simp only [interp] at h
    obtain ⟨s', hv, _⟩ := bok.mp h
    exact absurd hv fail_not_ok
  | ksb k ih =>
    intro s a r hI h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, hv, ih v s a r hI hk⟩
  | cpu k ih =>
    intro s a r hI h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, hv, ih v s a r hI hk⟩
  | masks k ih =>
    intro s a r hI h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, hv, ih v s a r hI hk⟩
  | arch op k ih =>
    intro s a r hI h
    simp only [interp] at h ⊢
    obtain ⟨⟨v, a'⟩, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨(v, a'), hv, ih v s a' r hI hk⟩

end

end Fl4ProofsA64.P2.PathObl
