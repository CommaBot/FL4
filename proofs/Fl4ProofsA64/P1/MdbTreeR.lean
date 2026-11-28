/-
P1 (aarch64, gen 54): **retype keeps `UtInvA`, at the level of the slot contents and the ghost tree** — x86
UntypedUtInv's `RetypeDelta` / `RetypeDelta.utinv` (`utinv_retype`) ported to A64 (`capA`, `OS`, MdbTreeA's ranges).

* **`RetypeDeltaA`** (x86 `RetypeDelta`, MdbStep): what `untyped::retype` does to the caps and the tree, abstractly —
  states `s0` (before), `s1` (after the source's free index is set: `untyped.retype`'s `set_cap` of
  `Untyped ptr size_bits (base + total - ptr)`), `sf` (after `create_new_objects`' loop of `insert_new_cap`); the new
  caps `cj j` (`j < w`) in the `OS` slots `dslot j`, null before, `k` bytes apart from `A`; the tree grown by the new
  slots as children of `src` (`insert_new_cap` puts each right after the parent). Changes from x86: membership is
  `OS` (A64's `UtInvA` quantifies over `OS`; a new slot was null), `dnd` (the new slots are in no old descent, x86's
  `dnot` through `MdbLinks`), no `cdev` (not used by the invariant).
* **`RetypeDeltaA.utinv`** (x86 `RetypeDelta.utinv`): `UtInvA` at the end, including the A64 field `anc` (new caps
  are children of an untyped cap). Each lemma here mirrors the x86 lemma of the same name: `srcR`, `srcR'`, `cls`,
  `not_desc_src_self`, `cj_in`, `cj_disj`, `reg'`, `rng_old`, `nfi_ge`, `inc'`, `cj_ut`, `noov'`, `excl_new_old`,
  `excl_new_src`, `excl'`, `fib'`, `src_anc`, `meet_new`, `drange'`; new: `anc'`.

Not here (still owed): building `RetypeDeltaA` from `untyped.retype` / `create_new_objects` at function level (an
`insert_new_cap` link lemma — `MdbLk` and `Mdb.MdbOK.insert` per step — the loop induction, and `create_object`'s
cap shapes for `cbase` / `ctop` / `cut`).

No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.MdbTreeA
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

namespace W7
namespace R
namespace ST

theorem ut_rng (p b i i' : U64) (d d' : Bool) :
    baseA (.Untyped p b i d) = baseA (.Untyped p b i' d') ∧ topA (.Untyped p b i d) = topA (.Untyped p b i' d') ∧
      physA (.Untyped p b i d) = physA (.Untyped p b i' d') ∧ isUtA (.Untyped p b i d) = isUtA (.Untyped p b i' d') := by
  refine ⟨?_, ?_, by rw [physA_ut, physA_ut], rfl⟩
  · unfold baseA; rw [ptrA_ut, ptrA_ut]
  · unfold topA; rw [ptrA_ut, ptrA_ut, sizeA_ut, sizeA_ut]

/-- **What retype did to the slots and the tree** (module docstring; x86 `RetypeDelta`). -/
structure RetypeDeltaA (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (par0 parf : U64 → Option U64)
    (s0 s1 sf : S) (src p sb fi nfi : U64) (dev : Bool) (A k w : Nat) (dslot : Nat → U64)
    (cj : Nat → capability.Cap) : Prop where
  hP0 : ParIn OS par0
  hsrc : src ∈ OS
  hcs : capA st s0 src = .Untyped p sb fi dev
  hcs1 : capA st s1 src = .Untyped p sb nfi dev
  hc1 : ∀ x ∈ OS, x ≠ src → capA st s1 x = capA st s0 x
  hfi : fi.val < 2 ^ sb.val
  hA : p.val + fi.val ≤ A
  hnfi : p.val + nfi.val = A + w * k
  hAw : A + w * k ≤ p.val + 2 ^ sb.val
  hk : 1 ≤ k
  cphys : ∀ j, j < w → physA (cj j) = true
  cbase : ∀ j, j < w → baseA (cj j) = A + j * k
  ctop : ∀ j, j < w → topA (cj j) = A + j * k + k - 1
  cut : ∀ j, j < w → isUtA (cj j) = true → ∃ us d, cj j = .Untyped ⟨BitVec.ofNat 64 (A + j * k)⟩ us 0#u64 d ∧
    2 ^ us.val = k
  dnull : ∀ j, j < w → capA st s0 (dslot j) = .Null
  dinj : ∀ j l, j < w → l < w → dslot j = dslot l → j = l
  dnd : ∀ j, j < w → ∀ z, ¬ Mdb.Desc par0 (dslot j) z ∧ ¬ Mdb.Desc par0 z (dslot j)
  F2a : ∀ j, j < w → capA st sf (dslot j) = cj j
  F2b : ∀ x ∈ OS, (∀ j, j < w → x ≠ dslot j) → capA st sf x = capA st s1 x
  F3 : ∀ y x, Mdb.Desc parf y x ↔ Mdb.Desc par0 y x ∨
    ∃ j, j < w ∧ y = dslot j ∧ (x = src ∨ Mdb.Desc par0 src x)

namespace RetypeDeltaA
variable {OS : Set U64} {par0 parf : U64 → Option U64} {s0 s1 sf : S} {src p sb fi nfi : U64} {dev : Bool}
  {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap}
  (h : RetypeDeltaA st OS par0 parf s0 s1 sf src p sb fi nfi dev A k w dslot cj) (hU : UtInvA st OS par0 s0)
include h hU

theorem srcR : baseA (capability.Cap.Untyped p sb fi dev) = p.val ∧
    topA (capability.Cap.Untyped p sb fi dev) = p.val + 2 ^ sb.val - 1 ∧ p.val + 2 ^ sb.val ≤ 2 ^ 64 := by
  have hr := hU.reg src h.hsrc (by rw [h.hcs]; exact physA_ut _ _ _ _)
  rw [h.hcs] at hr
  exact ut_rangeA (capA_ut_b h.hcs) hr

theorem srcR' : baseA (capability.Cap.Untyped p sb nfi dev) = p.val ∧
    topA (capability.Cap.Untyped p sb nfi dev) = p.val + 2 ^ sb.val - 1 := by
  obtain ⟨e1, e2, -⟩ := ut_rng p sb nfi fi dev dev
  obtain ⟨h1, h2, -⟩ := h.srcR hU
  exact ⟨e1.trans h1, e2.trans h2⟩

theorem src_not_new {j : Nat} (hj : j < w) : src ≠ dslot j := fun e => by
  have := h.dnull j hj; rw [← e, h.hcs] at this; cases this

theorem srcF : capA st sf src = .Untyped p sb nfi dev := by
  rw [h.F2b src h.hsrc (fun j hj => h.src_not_new hU hj), h.hcs1]

theorem newOr {x : U64} : (∀ j, j < w → x ≠ dslot j) ∨ ∃ j, j < w ∧ x = dslot j := by
  by_cases hj : ∃ j, j < w ∧ x = dslot j
  · exact Or.inr hj
  · push_neg at hj; exact Or.inl hj

theorem cls {x : U64} (hx : x ∈ OS) :
    ((∀ j, j < w → x ≠ dslot j) ∧ x ≠ src ∧ capA st sf x = capA st s0 x) ∨
    (x = src ∧ capA st sf x = .Untyped p sb nfi dev) ∨ (∃ j, j < w ∧ x = dslot j ∧ capA st sf x = cj j) := by
  rcases h.newOr hU (x := x) with hn | ⟨j, hj, rfl⟩
  · by_cases hxs : x = src
    · exact Or.inr (Or.inl ⟨hxs, by rw [h.F2b x hx hn, hxs, h.hcs1]⟩)
    · exact Or.inl ⟨hn, hxs, by rw [h.F2b x hx hn, h.hc1 x hx hxs]⟩
  · exact Or.inr (Or.inr ⟨j, hj, rfl, h.F2a j hj⟩)

theorem not_desc_src_self : ¬ Mdb.Desc par0 src src := by
  intro hd
  have := (hU.inc src h.hsrc p sb fi dev h.hcs src hd).2.2
  rw [h.hcs, (h.srcR hU).2.1] at this
  have := h.hfi; omega

theorem cj_in {j : Nat} (hj : j < w) : p.val ≤ baseA (cj j) ∧ topA (cj j) ≤ p.val + 2 ^ sb.val - 1 := by
  rw [h.cbase j hj, h.ctop j hj]
  have h1 : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at h1
  have := h.hA; have := h.hAw; have := h.hk
  omega

theorem cj_disj {j l : Nat} (hj : j < w) (hl : l < w) (hjl : j ≠ l) :
    topA (cj j) < baseA (cj l) ∨ topA (cj l) < baseA (cj j) := by
  rw [h.ctop j hj, h.cbase l hl, h.ctop l hl, h.cbase j hj]
  have := h.hk
  rcases Nat.lt_or_gt_of_ne hjl with hlt | hlt
  · left; have : (j + 1) * k ≤ l * k := Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  · right; have : (l + 1) * k ≤ j * k := Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, Nat.one_mul] at this; omega

/-- Old slots keep their ranges (the source's cap changes only its free index). -/
theorem rng_old {y : U64} (hy : y ∈ OS) (hyn : ∀ j, j < w → y ≠ dslot j) :
    baseA (capA st sf y) = baseA (capA st s0 y) ∧ topA (capA st sf y) = topA (capA st s0 y) ∧
      physA (capA st sf y) = physA (capA st s0 y) ∧ isUtA (capA st sf y) = isUtA (capA st s0 y) := by
  rw [h.F2b y hy hyn]
  by_cases hys : y = src
  · rw [hys, h.hcs1, h.hcs]; exact ut_rng _ _ _ _ _ _
  · rw [h.hc1 y hy hys]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem nfi_ge : p.val + fi.val ≤ p.val + nfi.val := by have := h.hA; have := h.hnfi; omega

theorem old_of_desc {y x : U64} (hd : Mdb.Desc par0 y x) :
    (∀ j, j < w → y ≠ dslot j) ∧ (∀ j, j < w → x ≠ dslot j) :=
  ⟨fun j hj e => (h.dnd j hj x).1 (by rw [← e]; exact hd), fun j hj e => (h.dnd j hj y).2 (by rw [← e]; exact hd)⟩

theorem reg' : ∀ x ∈ OS, physA (capA st sf x) = true → baseA (capA st sf x) ≤ topA (capA st sf x) := by
  intro x hx hp
  rcases h.cls hU hx with ⟨-, -, he⟩ | ⟨-, he⟩ | ⟨j, hj, -, he⟩
  · rw [he] at hp ⊢; exact hU.reg x hx hp
  · rw [he, (h.srcR' hU).1, (h.srcR' hU).2]; have : 1 ≤ 2 ^ sb.val := Nat.one_le_two_pow; omega
  · rw [he, h.cbase j hj, h.ctop j hj]; have := h.hk; omega

theorem inc' : ∀ x ∈ OS, ∀ p' sb' fi' d', capA st sf x = .Untyped p' sb' fi' d' →
    ∀ y, Mdb.Desc parf y x →
      physA (capA st sf y) = true ∧ p'.val ≤ baseA (capA st sf y) ∧ topA (capA st sf y) < p'.val + fi'.val := by
  intro x hx p' sb' fi' d' hcx y hy
  rcases h.cls hU hx with ⟨hxn, hxs, he⟩ | ⟨hxe, he⟩ | ⟨j, hj, rfl, he⟩
  · rw [he] at hcx
    rcases (h.F3 y x).1 hy with hd | ⟨l, hl, rfl, hxs' | hd⟩
    · obtain ⟨e1, e2, e3, -⟩ := h.rng_old hU (desc_in h.hP0 hd).1 (h.old_of_desc hU hd).1
      rw [e1, e2, e3]; exact hU.inc x hx p' sb' fi' d' hcx y hd
    · exact absurd hxs' hxs
    · obtain ⟨h1, h2, h3⟩ := hU.inc x hx p' sb' fi' d' hcx src hd
      rw [h.hcs, (h.srcR hU).1] at h2; rw [h.hcs, (h.srcR hU).2.1] at h3
      obtain ⟨c1, c2⟩ := h.cj_in hU hl
      rw [h.F2a l hl]; exact ⟨h.cphys l hl, by omega, by omega⟩
  · rw [hxe] at hy; rw [he] at hcx; cases hcx
    rcases (h.F3 y src).1 hy with hd | ⟨l, hl, rfl, -⟩
    · have hy0 := (desc_in h.hP0 hd).1
      obtain ⟨e1, e2, e3, -⟩ := h.rng_old hU hy0 (h.old_of_desc hU hd).1
      obtain ⟨h1, h2, h3⟩ := hU.inc src h.hsrc _ _ _ _ h.hcs y hd
      rw [e1, e2, e3]; have := h.nfi_ge hU; exact ⟨h1, h2, by omega⟩
    · rw [h.F2a l hl, h.cbase l hl, h.ctop l hl]
      have h1 : (l + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hl
      rw [Nat.add_mul, Nat.one_mul] at h1
      have := h.hA; have := h.hnfi; have := h.hk
      exact ⟨h.cphys l hl, by omega, by omega⟩
  · exfalso
    rcases (h.F3 y (dslot j)).1 hy with hd | ⟨l, hl, -, hs | hd⟩
    · exact (h.dnd j hj y).2 hd
    · exact h.src_not_new hU hj hs.symm
    · exact (h.dnd j hj src).2 hd

theorem cj_ut {j : Nat} (hj : j < w) {p' sb' fi' : U64} {d' : Bool} (he : cj j = .Untyped p' sb' fi' d') :
    p'.val = A + j * k ∧ 2 ^ sb'.val = k ∧ fi'.val = 0 := by
  obtain ⟨us, d, he', hk⟩ := h.cut j hj (by rw [he]; rfl)
  rw [he] at he'; cases he'
  have h1 : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at h1
  have := (h.srcR hU).2.2; have := h.hAw; have := h.hk
  refine ⟨?_, hk, rfl⟩
  show (BitVec.ofNat 64 (A + j * k)).toNat = _; simp; omega

set_option maxHeartbeats 2000000 in
theorem noov' : ∀ x ∈ OS, ∀ p' sb' fi' d', capA st sf x = .Untyped p' sb' fi' d' →
    ∀ y ∈ OS, physA (capA st sf y) = true →
      DisjRA (capA st sf y) (p'.val + fi'.val) (p'.val + 2 ^ sb'.val) ∨
        (isUtA (capA st sf y) = true ∧ WithinA (capA st sf x) (capA st sf y)) := by
  intro x hx p' sb' fi' d' hcx y hy hp
  obtain ⟨s1, s2, s3⟩ := h.srcR hU
  obtain ⟨s1', s2'⟩ := h.srcR' hU
  have hfi := h.hfi; have hA := h.hA; have hnfi := h.hnfi; have hAw := h.hAw; have hk := h.hk
  have hyc : ((∀ l, l < w → y ≠ dslot l) ∧ baseA (capA st sf y) = baseA (capA st s0 y) ∧
      topA (capA st sf y) = topA (capA st s0 y) ∧ physA (capA st sf y) = physA (capA st s0 y) ∧
      isUtA (capA st sf y) = isUtA (capA st s0 y)) ∨ (∃ l, l < w ∧ y = dslot l ∧ capA st sf y = cj l) := by
    rcases h.newOr hU (x := y) with hn | ⟨l, hl, rfl⟩
    · exact Or.inl ⟨hn, h.rng_old hU hy hn⟩
    · exact Or.inr ⟨l, hl, rfl, h.F2a l hl⟩
  rcases h.cls hU hx with ⟨hxn, hxs, he⟩ | ⟨hxe, he⟩ | ⟨j, hj, rfl, he⟩
  · -- an old untyped cap
    rw [he] at hcx
    have hsb' := capA_ut_b hcx
    have hxr := hU.reg x hx (by rw [hcx]; exact physA_ut _ _ _ _)
    rw [hcx] at hxr
    obtain ⟨x1, x2, x3⟩ := ut_rangeA hsb' hxr
    have hwx : ∀ c, WithinA (capA st sf x) c ↔ baseA c ≤ p'.val ∧ p'.val + 2 ^ sb'.val - 1 ≤ topA c := by
      intro c; unfold WithinA; rw [he, hcx, x1, x2]
    rcases hyc with ⟨-, e1, e2, e3, e4⟩ | ⟨l, hl, rfl, hcy⟩
    · rw [e3] at hp
      rcases hU.noov x hx p' sb' fi' d' hcx y hy hp with hd | ⟨hu, hw⟩
      · left; unfold DisjRA at hd ⊢; rw [e1, e2]; exact hd
      · right; refine ⟨by rw [e4]; exact hu, ?_⟩
        rw [hwx]; unfold WithinA at hw; rw [hcx, x1, x2] at hw; rw [e1, e2]; exact hw
    · rw [hcy]
      obtain ⟨c1, c2⟩ := h.cj_in hU hl
      rcases hU.noov x hx p' sb' fi' d' hcx src h.hsrc (by rw [h.hcs]; exact physA_ut _ _ _ _) with hd | ⟨-, hw⟩
      · left; unfold DisjRA at hd ⊢; rw [h.hcs, s1, s2] at hd; omega
      · unfold WithinA at hw; rw [hcx, x1, x2, h.hcs, s1, s2] at hw
        have cb := h.cbase l hl
        rcases hU.noov src h.hsrc p sb fi dev h.hcs x hx (by rw [hcx]; exact physA_ut _ _ _ _) with hd | ⟨-, hw2⟩
        · left; unfold DisjRA at hd ⊢; rw [hcx, x1, x2] at hd
          have : 1 ≤ 2 ^ sb'.val := Nat.one_le_two_pow
          rcases hd with hd | hd
          · right; omega
          · omega
        · unfold WithinA at hw2; rw [hcx, x1, x2, h.hcs, s1, s2] at hw2
          have hp' : p' = p := UScalar.eq_of_val_eq (by omega)
          have h2 : 2 ^ sb'.val = 2 ^ sb.val := by
            have : 1 ≤ 2 ^ sb'.val := Nat.one_le_two_pow; have : 1 ≤ 2 ^ sb.val := Nat.one_le_two_pow; omega
          have hsb'' : sb' = sb := UScalar.eq_of_val_eq (Nat.pow_right_injective (le_refl 2) h2)
          subst hp' hsb''
          rcases hU.excl x hx src h.hsrc hxs p' sb' fi' fi d' dev hcx h.hcs with hf | hf
          · left; unfold DisjRA; omega
          · omega
  · -- the untyped cap retyped from
    rw [he] at hcx; cases hcx
    rcases hyc with ⟨-, e1, e2, e3, e4⟩ | ⟨l, hl, rfl, hcy⟩
    · rw [e3] at hp
      rcases hU.noov src h.hsrc p sb fi dev h.hcs y hy hp with hd | ⟨hu, hw⟩
      · left; unfold DisjRA at hd ⊢; rw [e1, e2]; omega
      · right; refine ⟨by rw [e4]; exact hu, ?_⟩
        unfold WithinA at hw ⊢; rw [he, s1', s2']; rw [h.hcs, s1, s2] at hw; rw [e1, e2]; exact hw
    · left; rw [hcy]; unfold DisjRA; rw [h.ctop l hl]
      have h1 : (l + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hl
      rw [Nat.add_mul, Nat.one_mul] at h1; omega
  · -- a new untyped cap
    rw [he] at hcx
    obtain ⟨hp1, hp2, hp3⟩ := h.cj_ut hU hj hcx
    rw [hp1, hp2, hp3]
    obtain ⟨c1, c2⟩ := h.cj_in hU hj
    have cb := h.cbase j hj; have ct := h.ctop j hj
    have h1 : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at h1
    rcases hyc with ⟨-, e1, e2, e3, e4⟩ | ⟨l, hl, rfl, hcy⟩
    · rw [e3] at hp
      rcases hU.noov src h.hsrc p sb fi dev h.hcs y hy hp with hd | ⟨hu, hw⟩
      · left; unfold DisjRA at hd ⊢; rw [e1, e2]; omega
      · right; refine ⟨by rw [e4]; exact hu, ?_⟩
        unfold WithinA at hw ⊢; rw [h.hcs, s1, s2] at hw; rw [he, e1, e2]; omega
    · rw [hcy]
      by_cases hjl : j = l
      · subst hjl; right; refine ⟨by rw [hcx]; rfl, ?_⟩; rw [he]; exact ⟨le_rfl, le_rfl⟩
      · left; unfold DisjRA
        rcases h.cj_disj hU hj hl hjl with hd | hd <;> [right; left] <;> omega

theorem excl_new_old {j : Nat} (hj : j < w) {y : U64} (hy0 : y ∈ OS) (hys : y ≠ src)
    {p' sb' fi1 fi2 : U64} {d1 d2 : Bool} (hx : cj j = .Untyped p' sb' fi1 d1)
    (hy : capA st s0 y = .Untyped p' sb' fi2 d2) : 2 ^ sb'.val ≤ fi2.val := by
  obtain ⟨s1, s2, s3⟩ := h.srcR hU
  obtain ⟨hp1, hp2, -⟩ := h.cj_ut hU hj hx
  have hfi := h.hfi; have hA := h.hA; have hAw := h.hAw; have hk := h.hk
  have h1 : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at h1
  have hyr := hU.reg y hy0 (by rw [hy]; exact physA_ut _ _ _ _)
  rw [hy] at hyr
  obtain ⟨y1, y2, -⟩ := ut_rangeA (capA_ut_b hy) hyr
  rcases hU.noov src h.hsrc p sb fi dev h.hcs y hy0 (by rw [hy]; exact physA_ut _ _ _ _) with hd | ⟨-, hw⟩
  · exfalso; unfold DisjRA at hd; rw [hy, y1, y2] at hd; omega
  · unfold WithinA at hw; rw [hy, y1, y2, h.hcs, s1, s2] at hw
    obtain ⟨w1, w2⟩ := hw
    have hpe : p'.val = p.val := by omega
    have hp' : p' = p := UScalar.eq_of_val_eq hpe
    have h2 : 2 ^ sb'.val = 2 ^ sb.val := by
      have : 1 ≤ 2 ^ sb'.val := Nat.one_le_two_pow; have : 1 ≤ 2 ^ sb.val := Nat.one_le_two_pow; omega
    have hsb' : sb' = sb := UScalar.eq_of_val_eq (Nat.pow_right_injective (le_refl 2) h2)
    subst hp' hsb'
    rcases hU.excl y hy0 src h.hsrc hys p' sb' fi2 fi d2 dev hy h.hcs with hf | hf
    · exact hf
    · omega

theorem excl_new_src {j : Nat} (hj : j < w) {p' sb' fi1 : U64} {d1 : Bool} (hx : cj j = .Untyped p' sb' fi1 d1)
    (hp : p' = p) (hs : sb' = sb) : 2 ^ sb'.val ≤ nfi.val := by
  obtain ⟨s1, s2, s3⟩ := h.srcR hU
  obtain ⟨hp1, hp2, -⟩ := h.cj_ut hU hj hx
  subst hp hs
  have hfi := h.hfi; have hA := h.hA; have hAw := h.hAw; have hk := h.hk; have hn := h.hnfi
  have h1 : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at h1
  have hw1 : w * k ≤ 2 ^ sb'.val := by omega
  have : w ≤ 1 := by
    by_contra hc
    have : 2 * k ≤ w * k := Nat.mul_le_mul_right _ (by omega)
    omega
  have hw : w = 1 := by omega
  subst hw; omega

set_option maxHeartbeats 2000000 in
theorem excl' : ∀ x ∈ OS, ∀ y ∈ OS, x ≠ y → ∀ p' sb' fi1 fi2 d1 d2,
    capA st sf x = .Untyped p' sb' fi1 d1 → capA st sf y = .Untyped p' sb' fi2 d2 →
      2 ^ sb'.val ≤ fi1.val ∨ 2 ^ sb'.val ≤ fi2.val := by
  intro x hx y hy hxy p' sb' fi1 fi2 d1 d2 hcx hcy
  have hfi := h.hfi
  rcases h.cls hU hx with ⟨hxn, hxs, hex⟩ | ⟨hxe, hex⟩ | ⟨j, hj, rfl, hex⟩ <;>
    rcases h.cls hU hy with ⟨hyn, hys, hey⟩ | ⟨hye, hey⟩ | ⟨l, hl, rfl, hey⟩
  · rw [hex] at hcx; rw [hey] at hcy; exact hU.excl x hx y hy hxy _ _ _ _ _ _ hcx hcy
  · rw [hex] at hcx; rw [hey] at hcy; cases hcy
    rcases hU.excl x hx src h.hsrc hxs _ _ _ _ _ _ hcx h.hcs with hf | hf
    · exact Or.inl hf
    · omega
  · rw [hex] at hcx; rw [hey] at hcy
    exact Or.inl (h.excl_new_old hU hl hx hxs hcy hcx)
  · rw [hex] at hcx; rw [hey] at hcy; cases hcx
    rcases hU.excl src h.hsrc y hy (Ne.symm hys) _ _ _ _ _ _ h.hcs hcy with hf | hf
    · omega
    · exact Or.inr hf
  · exact absurd (hxe.trans hye.symm) hxy
  · rw [hex] at hcx; rw [hey] at hcy; cases hcx
    exact Or.inl (h.excl_new_src hU hl hcy rfl rfl)
  · rw [hex] at hcx; rw [hey] at hcy
    exact Or.inr (h.excl_new_old hU hj hy hys hcx hcy)
  · rw [hex] at hcx; rw [hey] at hcy; cases hcy
    exact Or.inr (h.excl_new_src hU hj hcx rfl rfl)
  · exfalso
    rw [hex] at hcx; rw [hey] at hcy
    have hjl : j ≠ l := fun e => hxy (by rw [e])
    have := h.cj_disj hU hj hl hjl
    obtain ⟨a1, -, -⟩ := h.cj_ut hU hj hcx
    obtain ⟨a2, -, -⟩ := h.cj_ut hU hl hcy
    rw [h.cbase j hj, h.ctop j hj, h.cbase l hl, h.ctop l hl] at this
    have := h.hk; omega

theorem fib' : ∀ x ∈ OS, ∀ p' sb' fi' d', capA st sf x = .Untyped p' sb' fi' d' → fi'.val ≤ 2 ^ sb'.val := by
  intro x hx p' sb' fi' d' hc
  rcases h.cls hU hx with ⟨-, -, he⟩ | ⟨-, he⟩ | ⟨j, hj, -, he⟩
  · rw [he] at hc; exact hU.fib x hx _ _ _ _ hc
  · rw [he] at hc; cases hc
    have := h.hnfi; have := h.hAw; have := h.hA; omega
  · rw [he] at hc
    obtain ⟨us, d, hcj, -⟩ := h.cut j hj (by rw [hc]; rfl)
    rw [hcj] at hc; cases hc; simp

/-- A cap containing the untyped cap is its ancestor (it cannot be a descendant, which lies below the free index). -/
theorem src_anc {z : U64} (hz : z ∈ OS) (hzs : z ≠ src) (hp : physA (capA st s0 z) = true)
    (hw : WithinA (.Untyped p sb fi dev) (capA st s0 z)) : Mdb.Desc par0 src z := by
  obtain ⟨s1, s2, -⟩ := h.srcR hU
  unfold WithinA at hw; rw [s1, s2] at hw
  have hfi := h.hfi
  have h1 : 1 ≤ 2 ^ sb.val := Nat.one_le_two_pow
  rcases hU.drange src h.hsrc p sb fi dev h.hcs z hz hzs hp (by
    unfold DisjA; rw [h.hcs, s1, s2]; omega) with hd | hd
  · exfalso
    have := (hU.inc src h.hsrc p sb fi dev h.hcs z hd).2.2
    omega
  · exact hd

/-- An old cap meeting a new one is the untyped cap or one of its ancestors. -/
theorem meet_new {j : Nat} (hj : j < w) {z : U64} (hz : z ∈ OS)
    (hp : physA (capA st s0 z) = true) (hd : ¬ DisjA (cj j) (capA st s0 z)) :
    z = src ∨ Mdb.Desc par0 src z := by
  by_cases hzs : z = src
  · exact Or.inl hzs
  right
  have cb := h.cbase j hj
  obtain ⟨-, c2⟩ := h.cj_in hU hj
  have hA := h.hA
  rcases hU.noov src h.hsrc p sb fi dev h.hcs z hz hp with hr | ⟨-, hw⟩
  · exfalso; apply hd; unfold DisjRA at hr; unfold DisjA
    rcases hr with hr | hr
    · right; have := Nat.zero_le j; omega
    · left; have : 1 ≤ 2 ^ sb.val := Nat.one_le_two_pow; omega
  · rw [h.hcs] at hw; exact h.src_anc hU hz hzs hp hw

set_option maxHeartbeats 2000000 in
theorem drange' : ∀ x ∈ OS, ∀ p' sb' fi' d', capA st sf x = .Untyped p' sb' fi' d' →
    ∀ y ∈ OS, y ≠ x → physA (capA st sf y) = true → ¬ DisjA (capA st sf y) (capA st sf x) →
      Mdb.Desc parf y x ∨ Mdb.Desc parf x y := by
  intro x hx p' sb' fi' d' hcx y hy hyx hp hd
  have lift : ∀ {a b}, Mdb.Desc par0 a b → Mdb.Desc parf a b := fun hd => (h.F3 _ _).2 (Or.inl hd)
  have newd : ∀ {l b}, l < w → (b = src ∨ Mdb.Desc par0 src b) → Mdb.Desc parf (dslot l) b :=
    fun hl hb => (h.F3 _ _).2 (Or.inr ⟨_, hl, rfl, hb⟩)
  have hdj : ∀ a b : capability.Cap, ¬ DisjA a b → (baseA a ≤ topA b ∧ baseA b ≤ topA a) := by
    intro a b hn; unfold DisjA at hn; omega
  rcases h.newOr hU (x := x) with hxn | ⟨j, hj, rfl⟩ <;> rcases h.newOr hU (x := y) with hyn | ⟨l, hl, rfl⟩
  · obtain ⟨x1, x2, -, x4⟩ := h.rng_old hU hx hxn
    obtain ⟨y1, y2, y3, -⟩ := h.rng_old hU hy hyn
    have hxu : isUtA (capA st s0 x) = true := by rw [← x4, hcx]; rfl
    obtain ⟨q, sz, f, dd, hq⟩ := isUtA_ex hxu
    rw [y3] at hp
    have hd' := hdj _ _ hd
    rw [x1, x2, y1, y2] at hd'
    rcases hU.drange x hx q sz f dd hq y hy hyx hp (by unfold DisjA; omega) with e | e
    · exact Or.inl (lift e)
    · exact Or.inr (lift e)
  · left
    by_cases hxs : x = src
    · rw [hxs]; exact newd hl (Or.inl rfl)
    obtain ⟨x1, x2, x3, -⟩ := h.rng_old hU hx hxn
    have hd' := hdj _ _ hd
    rw [x1, x2, h.F2a l hl] at hd'
    rcases h.meet_new hU hl hx (by rw [← x3, hcx]; exact physA_ut _ _ _ _) (by unfold DisjA; omega) with e | e
    · exact absurd e hxs
    · exact newd hl (Or.inr e)
  · right
    by_cases hys : y = src
    · rw [hys]; exact newd hj (Or.inl rfl)
    obtain ⟨y1, y2, y3, -⟩ := h.rng_old hU hy hyn
    have hd' := hdj _ _ hd
    rw [y1, y2, h.F2a j hj] at hd'
    rcases h.meet_new hU hj hy (by rw [← y3]; exact hp) (by unfold DisjA; omega) with e | e
    · exact absurd e hys
    · exact newd hj (Or.inr e)
  · exfalso
    have hjl : l ≠ j := fun e => hyx (by rw [e])
    have := h.cj_disj hU hl hj hjl
    have hd' := hdj _ _ hd
    rw [h.F2a l hl, h.F2a j hj] at hd'
    have := h.cbase j hj; have := h.ctop j hj; have := h.cbase l hl; have := h.ctop l hl; have := h.hk
    omega

/-- (A64 field) Ancestors of untyped caps stay untyped: the new slots are children of the source. -/
theorem anc' : ∀ x y, Mdb.Desc parf y x → isUtA (capA st sf y) = true → isUtA (capA st sf x) = true := by
  intro x y hd hu
  rcases (h.F3 y x).1 hd with hd0 | ⟨l, hl, rfl, hx'⟩
  · obtain ⟨hyO, hxO⟩ := desc_in h.hP0 hd0
    obtain ⟨hyn, hxn⟩ := h.old_of_desc hU hd0
    rw [(h.rng_old hU hyO hyn).2.2.2] at hu; rw [(h.rng_old hU hxO hxn).2.2.2]; exact hU.anc x y hd0 hu
  · rcases hx' with hxs | hd0
    · rw [hxs, h.srcF hU]; rfl
    · have hxO := (desc_in h.hP0 hd0).2
      rw [(h.rng_old hU hxO (h.old_of_desc hU hd0).2).2.2.2]
      exact hU.anc x src hd0 (by rw [h.hcs]; rfl)

/-- **Retype keeps the untyped invariant** (x86 `RetypeDelta.utinv`). -/
theorem utinv : UtInvA st OS parf sf :=
  ⟨h.reg' hU, h.inc' hU, h.noov' hU, h.excl' hU, h.fib' hU, h.drange' hU, h.anc' hU⟩

end RetypeDeltaA

end ST
end R
end W7

end

end Fl4ProofsA64.P1
