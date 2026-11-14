/-
P3 (DESIGN.md §9), untyped: **the untyped invariant `UtInv` is kept by
retype**, at the level of the slot contents and the ghost tree
(`utinv_retype`): from the state before the retype, the untyped cap's new
free index, and how the loop grew the tree (`LoopInv`'s tracking clauses).
-/
import Fl4Proofs.P3.UntypedLoop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section
set_option linter.unusedSimpArgs false

/-- **The untyped invariant** (hypothesis on the concrete state; l4v
`untyped_inc`, `caps_no_overlap` and the range part of `valid_cap`):
ranges of physical caps do not wrap; the descendants of an untyped cap lie in
it, below its free index; a cap whose range meets an untyped cap's free part
is an untyped cap containing it; and of two untyped caps of the same region,
one is full. -/
structure UtInv (mem : U64 → U64) (G : MdbGhost) : Prop where
  reg : ∀ x ∈ G.chains.flatten, physF (capV mem x) = true → baseF (capV mem x) ≤ topF (capV mem x)
  inc : ∀ x ∈ G.chains.flatten, ∀ p sb fi d, capV mem x = .Untyped p sb fi d → ∀ y, Mdb.Desc G.par y x →
    physF (capV mem y) = true ∧ p.val ≤ baseF (capV mem y) ∧ topF (capV mem y) < p.val + fi.val
  noov : ∀ x ∈ G.chains.flatten, ∀ p sb fi d, capV mem x = .Untyped p sb fi d →
    ∀ y ∈ G.chains.flatten, physF (capV mem y) = true →
      DisjR (capV mem y) (p.val + fi.val) (p.val + 2 ^ sb.val) ∨
        (isUt (capV mem y) = true ∧ Within (capV mem x) (capV mem y))
  excl : ∀ x ∈ G.chains.flatten, ∀ y ∈ G.chains.flatten, x ≠ y → ∀ p sb fi fi' d d',
    capV mem x = .Untyped p sb fi d → capV mem y = .Untyped p sb fi' d' → 2 ^ sb.val ≤ fi.val ∨ 2 ^ sb.val ≤ fi'.val
  fib : ∀ x ∈ G.chains.flatten, ∀ p sb fi d, capV mem x = .Untyped p sb fi d → fi.val ≤ 2 ^ sb.val
  /-- l4v `untyped_children_in_mdb` / `untyped_inc`: a physical cap whose
  range meets an untyped cap's is its descendant or its ancestor. -/
  drange : ∀ x ∈ G.chains.flatten, ∀ p sb fi d, capV mem x = .Untyped p sb fi d →
    ∀ y ∈ G.chains.flatten, y ≠ x → physF (capV mem y) = true → ¬ Disj (capV mem y) (capV mem x) →
      Mdb.Desc G.par y x ∨ Mdb.Desc G.par x y

theorem disj_comm {a b : capability.Cap} : Disj a b ↔ Disj b a := by unfold Disj; exact Or.comm

theorem capV_ut_sb {mem : U64 → U64} {x p sb fi : U64} {d : Bool} (h : capV mem x = .Untyped p sb fi d) :
    sb.val < 64 := capAt_untyped_inv (show capAt mem x = ok (.Untyped p sb fi d) by rw [capAt_capV, h])

/-- An untyped cap's range, when it does not wrap. -/
theorem ut_range {p sb fi : U64} {d : Bool} (hsb : sb.val < 64)
    (hr : baseF (.Untyped p sb fi d) ≤ topF (.Untyped p sb fi d)) :
    baseF (.Untyped p sb fi d) = p.val ∧ topF (.Untyped p sb fi d) = p.val + 2 ^ sb.val - 1 ∧
      p.val + 2 ^ sb.val ≤ 2 ^ 64 := by
  have hb : baseF (.Untyped p sb fi d) = p.val := by unfold baseF; rw [ptrF_ut]
  have hm := maskF_val (b := sb) hsb
  have h1 : 1 ≤ 2 ^ sb.val := Nat.one_le_two_pow
  have hp : 2 ^ sb.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hsb
  have ht : topF (.Untyped p sb fi d) = (p.val + (2 ^ sb.val - 1)) % 2 ^ 64 := by
    unfold topF; rw [ptrF_ut, sizeF_ut]
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hm]
  rw [hb, ht] at hr
  have hpv : p.val < 2 ^ 64 := by have := p.hBounds; simpa [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits] using this
  have hnw : p.val + (2 ^ sb.val - 1) < 2 ^ 64 := by
    by_contra hc
    have : (p.val + (2 ^ sb.val - 1)) % 2 ^ 64 = p.val + (2 ^ sb.val - 1) - 2 ^ 64 := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨hb, ?_, by omega⟩
  rw [ht, Nat.mod_eq_of_lt hnw]; omega

/-- What retype did to the slots and the tree, abstractly: `mem0`/`G0`
before, `mem1` after the free-index update, `memf`/`Gf` after the loop, new
caps `cj j` in slots `dslot j` (`j < w`), `k` bytes apart from `A`. -/
structure RetypeDelta (th : TypedHeap) (mem0 mem1 memf : U64 → U64) (G0 Gf : MdbGhost) (src : U64)
    (p sb fi nfi : U64) (dev : Bool) (A k w : Nat) (dslot : Nat → U64) (cj : Nat → capability.Cap) : Prop where
  hM0 : MdbLinks th mem0 G0
  hsrc : src ∈ G0.chains.flatten
  hcs : capV mem0 src = .Untyped p sb fi dev
  hcs1 : capV mem1 src = .Untyped p sb nfi dev
  hc1 : ∀ x ∈ G0.chains.flatten, x ≠ src → capV mem1 x = capV mem0 x
  hfi : fi.val < 2 ^ sb.val
  hA : p.val + fi.val ≤ A
  hnfi : p.val + nfi.val = A + w * k
  hAw : A + w * k ≤ p.val + 2 ^ sb.val
  hk : 1 ≤ k
  cphys : ∀ j, j < w → physF (cj j) = true
  cbase : ∀ j, j < w → baseF (cj j) = A + j * k
  ctop : ∀ j, j < w → topF (cj j) = A + j * k + k - 1
  cut : ∀ j, j < w → isUt (cj j) = true → ∃ us d, cj j = .Untyped ⟨BitVec.ofNat 64 (A + j * k)⟩ us 0#u64 d ∧
    2 ^ us.val = k
  dnot : ∀ j, j < w → dslot j ∉ G0.chains.flatten
  dinj : ∀ j l, j < w → l < w → dslot j = dslot l → j = l
  F1 : ∀ x ∈ Gf.chains.flatten, x ∈ G0.chains.flatten ∨ ∃ j, j < w ∧ x = dslot j
  F1b : ∀ x ∈ G0.chains.flatten, x ∈ Gf.chains.flatten
  F2a : ∀ j, j < w → capV memf (dslot j) = cj j
  F2b : ∀ x ∈ G0.chains.flatten, capV memf x = capV mem1 x
  F3 : ∀ y x, Mdb.Desc Gf.par y x ↔ Mdb.Desc G0.par y x ∨
    ∃ j, j < w ∧ y = dslot j ∧ (x = src ∨ Mdb.Desc G0.par src x)

namespace RetypeDelta
variable {th : TypedHeap} {mem0 mem1 memf : U64 → U64} {G0 Gf : MdbGhost} {src p sb fi nfi : U64} {dev : Bool}
  {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap}
  (h : RetypeDelta th mem0 mem1 memf G0 Gf src p sb fi nfi dev A k w dslot cj) (hU : UtInv mem0 G0)
include h hU

theorem srcR : baseF (capability.Cap.Untyped p sb fi dev) = p.val ∧
    topF (capability.Cap.Untyped p sb fi dev) = p.val + 2 ^ sb.val - 1 ∧ p.val + 2 ^ sb.val ≤ 2 ^ 64 := by
  have hr := hU.reg src h.hsrc (by rw [h.hcs]; exact physF_ut _ _ _ _)
  rw [h.hcs] at hr
  exact ut_range (capV_ut_sb h.hcs) hr

theorem srcR' : baseF (capability.Cap.Untyped p sb nfi dev) = p.val ∧
    topF (capability.Cap.Untyped p sb nfi dev) = p.val + 2 ^ sb.val - 1 := by
  obtain ⟨e1, e2, -⟩ := range_of_shape (show shape (capability.Cap.Untyped p sb nfi dev) =
    shape (capability.Cap.Untyped p sb fi dev) from rfl)
  obtain ⟨h1, h2, -⟩ := h.srcR hU
  exact ⟨e1.trans h1, e2.trans h2⟩

theorem cls {x : U64} (hx : x ∈ Gf.chains.flatten) :
    (x ∈ G0.chains.flatten ∧ x ≠ src ∧ capV memf x = capV mem0 x) ∨
    (x = src ∧ capV memf x = .Untyped p sb nfi dev) ∨ (∃ j, j < w ∧ x = dslot j ∧ capV memf x = cj j) := by
  rcases h.F1 x hx with hx0 | ⟨j, hj, rfl⟩
  · by_cases hxs : x = src
    · subst hxs; exact Or.inr (Or.inl ⟨rfl, by rw [h.F2b _ hx0, h.hcs1]⟩)
    · exact Or.inl ⟨hx0, hxs, by rw [h.F2b _ hx0, h.hc1 _ hx0 hxs]⟩
  · exact Or.inr (Or.inr ⟨j, hj, rfl, h.F2a j hj⟩)

theorem not_desc_src_self : ¬ Mdb.Desc G0.par src src := by
  intro hd
  have := (hU.inc src h.hsrc p sb fi dev h.hcs src hd).2.2
  rw [h.hcs, (h.srcR hU).2.1] at this
  have := h.hfi; omega

theorem cj_in {j : Nat} (hj : j < w) : p.val ≤ baseF (cj j) ∧ topF (cj j) ≤ p.val + 2 ^ sb.val - 1 := by
  rw [h.cbase j hj, h.ctop j hj]
  have h1 : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at h1
  have := h.hA; have := h.hAw; have := h.hk
  omega

theorem cj_disj {j l : Nat} (hj : j < w) (hl : l < w) (hjl : j ≠ l) :
    topF (cj j) < baseF (cj l) ∨ topF (cj l) < baseF (cj j) := by
  rw [h.cbase j hj, h.ctop j hj, h.cbase l hl, h.ctop l hl]
  have := h.hk
  rcases Nat.lt_or_gt_of_ne hjl with hlt | hlt
  · left; have : (j + 1) * k ≤ l * k := Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  · right; have : (l + 1) * k ≤ j * k := Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, Nat.one_mul] at this; omega

theorem reg' : ∀ x ∈ Gf.chains.flatten, physF (capV memf x) = true →
    baseF (capV memf x) ≤ topF (capV memf x) := by
  intro x hx hp
  rcases h.cls hU hx with ⟨hx0, -, he⟩ | ⟨rfl, he⟩ | ⟨j, hj, rfl, he⟩
  · rw [he] at hp ⊢; exact hU.reg x hx0 hp
  · rw [he, (h.srcR' hU).1, (h.srcR' hU).2]; have := Nat.one_le_two_pow (n := sb.val); omega
  · rw [he, h.cbase j hj, h.ctop j hj]; have := h.hk; omega

end RetypeDelta

namespace RetypeDelta
variable {th : TypedHeap} {mem0 mem1 memf : U64 → U64} {G0 Gf : MdbGhost} {src p sb fi nfi : U64} {dev : Bool}
  {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap}
  (h : RetypeDelta th mem0 mem1 memf G0 Gf src p sb fi nfi dev A k w dslot cj) (hU : UtInv mem0 G0)
include h hU

/-- Old slots keep their ranges (the untyped cap's changes only its free index). -/
theorem rng_old {y : U64} (hy : y ∈ G0.chains.flatten) :
    baseF (capV memf y) = baseF (capV mem0 y) ∧ topF (capV memf y) = topF (capV mem0 y) ∧
      physF (capV memf y) = physF (capV mem0 y) ∧ isUt (capV memf y) = isUt (capV mem0 y) := by
  rw [h.F2b y hy]
  by_cases hys : y = src
  · subst hys; rw [h.hcs1, h.hcs]
    exact ⟨(range_of_shape rfl).1, (range_of_shape rfl).2.1, (range_of_shape rfl).2.2, rfl⟩
  · rw [h.hc1 y hy hys]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem nfi_ge : p.val + fi.val ≤ p.val + nfi.val := by have := h.hA; have := h.hnfi; omega

theorem inc' : ∀ x ∈ Gf.chains.flatten, ∀ p' sb' fi' d', capV memf x = .Untyped p' sb' fi' d' →
    ∀ y, Mdb.Desc Gf.par y x →
      physF (capV memf y) = true ∧ p'.val ≤ baseF (capV memf y) ∧ topF (capV memf y) < p'.val + fi'.val := by
  intro x hx p' sb' fi' d' hcx y hy
  have hdm := fun {a b} (hd : Mdb.Desc G0.par a b) => desc_mem h.hM0 hd
  rcases h.cls hU hx with ⟨hx0, hxs, he⟩ | ⟨hxe, he⟩ | ⟨j, hj, rfl, he⟩
  · rw [he] at hcx
    rcases (h.F3 y x).1 hy with hd | ⟨l, hl, rfl, hxs' | hd⟩
    · obtain ⟨e1, e2, e3, -⟩ := h.rng_old hU (hdm hd).1
      rw [e1, e2, e3]; exact hU.inc x hx0 p' sb' fi' d' hcx y hd
    · exact absurd hxs' hxs
    · obtain ⟨h1, h2, h3⟩ := hU.inc x hx0 p' sb' fi' d' hcx src hd
      rw [h.hcs, (h.srcR hU).1] at h2; rw [h.hcs, (h.srcR hU).2.1] at h3
      obtain ⟨c1, c2⟩ := h.cj_in hU hl
      rw [h.F2a l hl]; exact ⟨h.cphys l hl, by omega, by omega⟩
  · rw [hxe] at hy; rw [he] at hcx; cases hcx
    rcases (h.F3 y src).1 hy with hd | ⟨l, hl, rfl, -⟩
    · have hy0 := (hdm hd).1
      obtain ⟨e1, e2, e3, -⟩ := h.rng_old hU hy0
      obtain ⟨h1, h2, h3⟩ := hU.inc src h.hsrc _ _ _ _ h.hcs y hd
      rw [e1, e2, e3]; have := h.nfi_ge hU; exact ⟨h1, h2, by omega⟩
    · rw [h.F2a l hl, h.cbase l hl, h.ctop l hl]
      have h1 : (l + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hl
      rw [Nat.add_mul, Nat.one_mul] at h1
      have := h.hA; have := h.hnfi; have := h.hk
      exact ⟨h.cphys l hl, by omega, by omega⟩
  · exfalso
    have hn := h.dnot j hj
    rcases (h.F3 y (dslot j)).1 hy with hd | ⟨l, hl, -, hs | hd⟩
    · exact hn (hdm hd).2
    · exact hn (hs ▸ h.hsrc)
    · exact hn (hdm hd).2

end RetypeDelta

namespace RetypeDelta
variable {th : TypedHeap} {mem0 mem1 memf : U64 → U64} {G0 Gf : MdbGhost} {src p sb fi nfi : U64} {dev : Bool}
  {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap}
  (h : RetypeDelta th mem0 mem1 memf G0 Gf src p sb fi nfi dev A k w dslot cj) (hU : UtInv mem0 G0)
include h hU

theorem cj_ut {j : Nat} (hj : j < w) {p' sb' fi' : U64} {d' : Bool} (he : cj j = .Untyped p' sb' fi' d') :
    p'.val = A + j * k ∧ 2 ^ sb'.val = k ∧ fi'.val = 0 := by
  obtain ⟨us, d, he', hk⟩ := h.cut j hj (by rw [he]; rfl)
  rw [he] at he'; cases he'
  have h1 : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at h1
  have := (h.srcR hU).2.2; have := h.hAw; have := h.hk
  refine ⟨?_, hk, rfl⟩
  show (BitVec.ofNat 64 (A + j * k)).toNat = _; simp; omega

theorem noov' : ∀ x ∈ Gf.chains.flatten, ∀ p' sb' fi' d', capV memf x = .Untyped p' sb' fi' d' →
    ∀ y ∈ Gf.chains.flatten, physF (capV memf y) = true →
      DisjR (capV memf y) (p'.val + fi'.val) (p'.val + 2 ^ sb'.val) ∨
        (isUt (capV memf y) = true ∧ Within (capV memf x) (capV memf y)) := by
  intro x hx p' sb' fi' d' hcx y hy hp
  obtain ⟨s1, s2, s3⟩ := h.srcR hU
  obtain ⟨s1', s2'⟩ := h.srcR' hU
  have hfi := h.hfi; have hA := h.hA; have hnfi := h.hnfi; have hAw := h.hAw; have hk := h.hk
  -- the ranges of `y`
  have hyc : (y ∈ G0.chains.flatten ∧ baseF (capV memf y) = baseF (capV mem0 y) ∧
      topF (capV memf y) = topF (capV mem0 y) ∧ physF (capV memf y) = physF (capV mem0 y) ∧
      isUt (capV memf y) = isUt (capV mem0 y)) ∨ (∃ l, l < w ∧ y = dslot l ∧ capV memf y = cj l) := by
    rcases h.F1 y hy with hy0 | ⟨l, hl, rfl⟩
    · exact Or.inl ⟨hy0, h.rng_old hU hy0⟩
    · exact Or.inr ⟨l, hl, rfl, h.F2a l hl⟩
  rcases h.cls hU hx with ⟨hx0, hxs, he⟩ | ⟨hxe, he⟩ | ⟨j, hj, rfl, he⟩
  · -- an old untyped cap
    rw [he] at hcx
    have hsb' := capV_ut_sb hcx
    have hxr := hU.reg x hx0 (by rw [hcx]; exact physF_ut _ _ _ _)
    rw [hcx] at hxr
    obtain ⟨x1, x2, x3⟩ := ut_range hsb' hxr
    have hwx : ∀ c, Within (capV memf x) c ↔ baseF c ≤ p'.val ∧ p'.val + 2 ^ sb'.val - 1 ≤ topF c := by
      intro c; unfold Within; rw [he, hcx, x1, x2]
    rcases hyc with ⟨hy0, e1, e2, e3, e4⟩ | ⟨l, hl, rfl, hcy⟩
    · rw [e3] at hp
      rcases hU.noov x hx0 p' sb' fi' d' hcx y hy0 hp with hd | ⟨hu, hw⟩
      · left; unfold DisjR at hd ⊢; rw [e1, e2]; exact hd
      · right; refine ⟨by rw [e4]; exact hu, ?_⟩
        rw [hwx]; unfold Within at hw; rw [hcx, x1, x2] at hw; rw [e1, e2]; exact hw
    · rw [hcy]
      obtain ⟨c1, c2⟩ := h.cj_in hU hl
      rcases hU.noov x hx0 p' sb' fi' d' hcx src h.hsrc (by rw [h.hcs]; exact physF_ut _ _ _ _) with hd | ⟨-, hw⟩
      · left; unfold DisjR at hd ⊢; rw [h.hcs, s1, s2] at hd; omega
      · unfold Within at hw; rw [hcx, x1, x2, h.hcs, s1, s2] at hw
        have cb := h.cbase l hl
        rcases hU.noov src h.hsrc p sb fi dev h.hcs x hx0 (by rw [hcx]; exact physF_ut _ _ _ _) with hd | ⟨-, hw2⟩
        · left; unfold DisjR at hd ⊢; rw [hcx, x1, x2] at hd
          have := Nat.one_le_two_pow (n := sb'.val)
          rcases hd with hd | hd
          · right; omega
          · omega
        · unfold Within at hw2; rw [hcx, x1, x2, h.hcs, s1, s2] at hw2
          have hp' : p' = p := UScalar.eq_of_val_eq (by omega)
          have h2 : 2 ^ sb'.val = 2 ^ sb.val := by
            have := Nat.one_le_two_pow (n := sb'.val); have := Nat.one_le_two_pow (n := sb.val); omega
          have hsb'' : sb' = sb := UScalar.eq_of_val_eq (Nat.pow_right_injective (le_refl 2) h2)
          subst hp' hsb''
          rcases hU.excl x hx0 src h.hsrc hxs p' sb' fi' fi d' dev hcx h.hcs with hf | hf
          · left; unfold DisjR; omega
          · omega
  · -- the untyped cap retyped from
    rw [he] at hcx; cases hcx
    rcases hyc with ⟨hy0, e1, e2, e3, e4⟩ | ⟨l, hl, rfl, hcy⟩
    · rw [e3] at hp
      rcases hU.noov src h.hsrc p sb fi dev h.hcs y hy0 hp with hd | ⟨hu, hw⟩
      · left; unfold DisjR at hd ⊢; rw [e1, e2]; omega
      · right; refine ⟨by rw [e4]; exact hu, ?_⟩
        unfold Within at hw ⊢; rw [he, s1', s2']; rw [h.hcs, s1, s2] at hw; rw [e1, e2]; exact hw
    · left; rw [hcy]; unfold DisjR; rw [h.ctop l hl]
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
    rcases hyc with ⟨hy0, e1, e2, e3, e4⟩ | ⟨l, hl, rfl, hcy⟩
    · rw [e3] at hp
      rcases hU.noov src h.hsrc p sb fi dev h.hcs y hy0 hp with hd | ⟨hu, hw⟩
      · left; unfold DisjR at hd ⊢; rw [e1, e2]; omega
      · right; refine ⟨by rw [e4]; exact hu, ?_⟩
        unfold Within at hw ⊢; rw [h.hcs, s1, s2] at hw; rw [he, e1, e2]; omega
    · rw [hcy]
      by_cases hjl : j = l
      · subst hjl; right; refine ⟨by rw [hcx]; rfl, ?_⟩; rw [he]; exact ⟨le_rfl, le_rfl⟩
      · left; unfold DisjR
        rcases h.cj_disj hU hj hl hjl with hd | hd <;> [right; left] <;> omega

end RetypeDelta

namespace RetypeDelta
variable {th : TypedHeap} {mem0 mem1 memf : U64 → U64} {G0 Gf : MdbGhost} {src p sb fi nfi : U64} {dev : Bool}
  {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap}
  (h : RetypeDelta th mem0 mem1 memf G0 Gf src p sb fi nfi dev A k w dslot cj) (hU : UtInv mem0 G0)
include h hU

theorem excl_new_old {j : Nat} (hj : j < w) {y : U64} (hy0 : y ∈ G0.chains.flatten) (hys : y ≠ src)
    {p' sb' fi1 fi2 : U64} {d1 d2 : Bool} (hx : cj j = .Untyped p' sb' fi1 d1)
    (hy : capV mem0 y = .Untyped p' sb' fi2 d2) : 2 ^ sb'.val ≤ fi2.val := by
  obtain ⟨s1, s2, s3⟩ := h.srcR hU
  obtain ⟨hp1, hp2, -⟩ := h.cj_ut hU hj hx
  have hfi := h.hfi; have hA := h.hA; have hAw := h.hAw; have hk := h.hk
  have h1 : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at h1
  have hyr := hU.reg y hy0 (by rw [hy]; exact physF_ut _ _ _ _)
  rw [hy] at hyr
  obtain ⟨y1, y2, -⟩ := ut_range (capV_ut_sb hy) hyr
  rcases hU.noov src h.hsrc p sb fi dev h.hcs y hy0 (by rw [hy]; exact physF_ut _ _ _ _) with hd | ⟨-, hw⟩
  · exfalso; unfold DisjR at hd; rw [hy, y1, y2] at hd; omega
  · unfold Within at hw; rw [hy, y1, y2, h.hcs, s1, s2] at hw
    obtain ⟨w1, w2⟩ := hw
    have hpe : p'.val = p.val := by omega
    have hp' : p' = p := UScalar.eq_of_val_eq hpe
    have h2 : 2 ^ sb'.val = 2 ^ sb.val := by
      have := Nat.one_le_two_pow (n := sb'.val); have := Nat.one_le_two_pow (n := sb.val); omega
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

theorem excl' : ∀ x ∈ Gf.chains.flatten, ∀ y ∈ Gf.chains.flatten, x ≠ y → ∀ p' sb' fi1 fi2 d1 d2,
    capV memf x = .Untyped p' sb' fi1 d1 → capV memf y = .Untyped p' sb' fi2 d2 →
      2 ^ sb'.val ≤ fi1.val ∨ 2 ^ sb'.val ≤ fi2.val := by
  intro x hx y hy hxy p' sb' fi1 fi2 d1 d2 hcx hcy
  have hfi := h.hfi
  rcases h.cls hU hx with ⟨hx0, hxs, hex⟩ | ⟨hxe, hex⟩ | ⟨j, hj, rfl, hex⟩ <;>
    rcases h.cls hU hy with ⟨hy0, hys, hey⟩ | ⟨hye, hey⟩ | ⟨l, hl, rfl, hey⟩
  · rw [hex] at hcx; rw [hey] at hcy; exact hU.excl x hx0 y hy0 hxy _ _ _ _ _ _ hcx hcy
  · rw [hex] at hcx; rw [hey] at hcy; cases hcy
    rcases hU.excl x hx0 src h.hsrc hxs _ _ _ _ _ _ hcx h.hcs with hf | hf
    · exact Or.inl hf
    · omega
  · rw [hex] at hcx; rw [hey] at hcy
    exact Or.inl (h.excl_new_old hU hl hx0 hxs hcy hcx)
  · rw [hex] at hcx; rw [hey] at hcy; cases hcx
    rcases hU.excl src h.hsrc y hy0 (Ne.symm hys) _ _ _ _ _ _ h.hcs hcy with hf | hf
    · omega
    · exact Or.inr hf
  · exact absurd (hxe.trans hye.symm) hxy
  · rw [hex] at hcx; rw [hey] at hcy; cases hcx
    exact Or.inl (h.excl_new_src hU hl hcy rfl rfl)
  · rw [hex] at hcx; rw [hey] at hcy
    exact Or.inr (h.excl_new_old hU hj hy0 hys hcx hcy)
  · rw [hex] at hcx; rw [hey] at hcy; cases hcy
    exact Or.inr (h.excl_new_src hU hj hcx rfl rfl)
  · exfalso
    rw [hex] at hcx; rw [hey] at hcy
    obtain ⟨a1, -, -⟩ := h.cj_ut hU hj hcx
    obtain ⟨a2, -, -⟩ := h.cj_ut hU hl hcy
    have hjl : j ≠ l := fun e => hxy (by rw [e])
    have := h.cj_disj hU hj hl hjl
    rw [h.cbase j hj, h.ctop j hj, h.cbase l hl, h.ctop l hl] at this
    have := h.hk; omega

theorem fib' : ∀ x ∈ Gf.chains.flatten, ∀ p' sb' fi' d', capV memf x = .Untyped p' sb' fi' d' →
    fi'.val ≤ 2 ^ sb'.val := by
  intro x hx p' sb' fi' d' hc
  rcases h.cls hU hx with ⟨hx0, -, he⟩ | ⟨-, he⟩ | ⟨j, hj, -, he⟩
  · rw [he] at hc; exact hU.fib x hx0 _ _ _ _ hc
  · rw [he] at hc; cases hc
    have := h.hnfi; have := h.hAw; have := h.hA; omega
  · rw [he] at hc
    obtain ⟨us, d, hcj, -⟩ := h.cut j hj (by rw [hc]; rfl)
    rw [hcj] at hc; cases hc; simp

/-- A cap containing the untyped cap is its ancestor (it cannot be a
descendant, which lies below the free index). -/
theorem src_anc {z : U64} (hz : z ∈ G0.chains.flatten) (hzs : z ≠ src) (hp : physF (capV mem0 z) = true)
    (hw : Within (.Untyped p sb fi dev) (capV mem0 z)) : Mdb.Desc G0.par src z := by
  obtain ⟨s1, s2, -⟩ := h.srcR hU
  unfold Within at hw; rw [s1, s2] at hw
  have hfi := h.hfi
  have h1 := Nat.one_le_two_pow (n := sb.val)
  rcases hU.drange src h.hsrc p sb fi dev h.hcs z hz hzs hp (by
    unfold Disj; rw [h.hcs, s1, s2]; omega) with hd | hd
  · exfalso
    have := (hU.inc src h.hsrc p sb fi dev h.hcs z hd).2.2
    omega
  · exact hd

/-- An old cap meeting a new one is the untyped cap or one of its ancestors. -/
theorem meet_new {j : Nat} (hj : j < w) {z : U64} (hz : z ∈ G0.chains.flatten)
    (hp : physF (capV mem0 z) = true) (hd : ¬ Disj (cj j) (capV mem0 z)) :
    z = src ∨ Mdb.Desc G0.par src z := by
  by_cases hzs : z = src
  · exact Or.inl hzs
  right
  have cb := h.cbase j hj
  obtain ⟨-, c2⟩ := h.cj_in hU hj
  have hA := h.hA
  rcases hU.noov src h.hsrc p sb fi dev h.hcs z hz hp with hr | ⟨-, hw⟩
  · exfalso; apply hd; unfold DisjR at hr; unfold Disj
    rcases hr with hr | hr
    · right; have := Nat.zero_le j; omega
    · left; have := Nat.one_le_two_pow (n := sb.val); omega
  · rw [h.hcs] at hw; exact h.src_anc hU hz hzs hp hw

theorem drange' : ∀ x ∈ Gf.chains.flatten, ∀ p' sb' fi' d', capV memf x = .Untyped p' sb' fi' d' →
    ∀ y ∈ Gf.chains.flatten, y ≠ x → physF (capV memf y) = true → ¬ Disj (capV memf y) (capV memf x) →
      Mdb.Desc Gf.par y x ∨ Mdb.Desc Gf.par x y := by
  intro x hx p' sb' fi' d' hcx y hy hyx hp hd
  have lift : ∀ {a b}, Mdb.Desc G0.par a b → Mdb.Desc Gf.par a b := fun hd => (h.F3 _ _).2 (Or.inl hd)
  have newd : ∀ {l b}, l < w → (b = src ∨ Mdb.Desc G0.par src b) → Mdb.Desc Gf.par (dslot l) b :=
    fun hl hb => (h.F3 _ _).2 (Or.inr ⟨_, hl, rfl, hb⟩)
  have hdj : ∀ a b : capability.Cap, ¬ Disj a b → (baseF a ≤ topF b ∧ baseF b ≤ topF a) := by
    intro a b hn; unfold Disj at hn; omega
  rcases h.F1 x hx with hx0 | ⟨j, hj, rfl⟩ <;> rcases h.F1 y hy with hy0 | ⟨l, hl, rfl⟩
  · obtain ⟨x1, x2, -, x4⟩ := h.rng_old hU hx0
    obtain ⟨y1, y2, y3, -⟩ := h.rng_old hU hy0
    have hxu : isUt (capV mem0 x) = true := by rw [← x4, hcx]; rfl
    obtain ⟨q, sz, f, dd, hq⟩ := isUt_iff.1 hxu
    rw [y3] at hp
    have hd' := hdj _ _ hd
    rw [x1, x2, y1, y2] at hd'
    rcases hU.drange x hx0 q sz f dd hq y hy0 hyx hp (by unfold Disj; omega) with e | e
    · exact Or.inl (lift e)
    · exact Or.inr (lift e)
  · left
    by_cases hxs : x = src
    · subst hxs; exact newd hl (Or.inl rfl)
    obtain ⟨x1, x2, x3, -⟩ := h.rng_old hU hx0
    have hd' := hdj _ _ hd
    rw [x1, x2, h.F2a l hl] at hd'
    rcases h.meet_new hU hl hx0 (by rw [← x3, hcx]; exact physF_ut _ _ _ _) (by unfold Disj; omega) with e | e
    · exact absurd e hxs
    · exact newd hl (Or.inr e)
  · right
    by_cases hys : y = src
    · subst hys; exact newd hj (Or.inl rfl)
    obtain ⟨y1, y2, y3, -⟩ := h.rng_old hU hy0
    have hd' := hdj _ _ hd
    rw [y1, y2, h.F2a j hj] at hd'
    rcases h.meet_new hU hj hy0 (by rw [← y3]; exact hp) (by unfold Disj; omega) with e | e
    · exact absurd e hys
    · exact newd hj (Or.inr e)
  · exfalso
    have hjl : l ≠ j := fun e => hyx (by rw [e])
    have := h.cj_disj hU hl hj hjl
    have hd' := hdj _ _ hd
    rw [h.F2a l hl, h.F2a j hj] at hd'
    have := h.cbase j hj; have := h.ctop j hj; have := h.cbase l hl; have := h.ctop l hl; have := h.hk
    omega

/-- **Retype keeps the untyped invariant.** -/
theorem utinv : UtInv memf Gf := ⟨h.reg' hU, h.inc' hU, h.noov' hU, h.excl' hU, h.fib' hU, h.drange' hU⟩

end RetypeDelta

end
end Fl4Proofs.P3
