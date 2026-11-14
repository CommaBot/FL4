/-
P3 (DESIGN.md §9), untyped: **the untyped invariant `UtInv` is kept by the
CNode operations** (`cdt::insert` of a derived cap, with
`set_untyped_cap_as_full`; `cdt::move_cap`; `cdt::swap`; `cdt::empty_slot`),
first abstractly on slot contents and the ghost tree (`UtInv.rename`,
`UtInv.remove`, `InsCtx.utinv`), then for FL4's functions.
-/
import Fl4Proofs.P3.UntypedUtInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- Two caps alike for `UtInv`: the same range, physicality, and the same
untyped cap if either is one. -/
structure UtEq (c' c : capability.Cap) : Prop where
  base : baseF c' = baseF c
  top : topF c' = topF c
  phys : physF c' = physF c
  ut : ∀ p sb fi d, c' = .Untyped p sb fi d ↔ c = .Untyped p sb fi d

theorem UtEq.refl (c : capability.Cap) : UtEq c c := ⟨rfl, rfl, rfl, fun _ _ _ _ => Iff.rfl⟩

/-- A cap of the same shape, equal to the old one if that is untyped (as
for the caps CNode operations write: derived, moved, mutated). -/
theorem UtEq.of_shape {c' c : capability.Cap} (hsh : shape c' = shape c) (hut : isUt c = true → c' = c) :
    UtEq c' c := by
  obtain ⟨h1, h2, h3⟩ := range_of_shape hsh
  refine ⟨h1, h2, h3, fun p sb fi d => ⟨fun e => ?_, fun e => ?_⟩⟩
  · have : isUt c = true := by rw [← isUt_of_shape hsh, e]; rfl
    rw [← hut this]; exact e
  · rw [hut (by rw [e]; rfl)]; exact e

theorem UtEq.isUt' {c' c : capability.Cap} (h : UtEq c' c) : isUt c' = isUt c := by
  cases hc : isUt c with
  | true =>
    obtain ⟨q, sz, f, d, e⟩ := isUt_iff.1 hc
    rw [(h.ut q sz f d).2 e]; rfl
  | false =>
    cases hc' : isUt c' with
    | false => rfl
    | true =>
      obtain ⟨q, sz, f, d, e⟩ := isUt_iff.1 hc'
      rw [(h.ut q sz f d).1 e] at hc; simp [isUt] at hc

theorem full_val {b : U64} (hb : b.val < 64) : (⟨1#64 <<< (b.val % 64)⟩ : U64).val = 2 ^ b.val := by
  show (1#64 <<< (b.val % 64)).toNat = 2 ^ b.val
  rw [BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt hb]
  simp [Nat.one_shiftLeft]
  exact Nat.pow_lt_pow_right (by decide) hb

/-! ## Renaming (`move_cap`, `swap`) -/

theorem UtInv.rename {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    (hU : UtInv mem G) (e : U64 ≃ U64)
    (hcap : ∀ a ∈ G.chains.flatten, UtEq (capV mem' (e a)) (capV mem a)) :
    UtInv mem' (renG G e) := by
  have hmem : ∀ z, z ∈ (renG G e).chains.flatten ↔ e.symm z ∈ G.chains.flatten := by
    intro z
    show z ∈ (G.chains.map (List.map e)).flatten ↔ _
    simp only [List.map_flatten.symm, List.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩; simpa using ha
    · intro h; exact ⟨_, h, by simp⟩
  have hD : ∀ y x, Mdb.Desc (renG G e).par y x ↔ Mdb.Desc G.par (e.symm y) (e.symm x) := by
    intro y x
    have := Mdb.desc_conj e G.par (e.symm y) (e.symm x)
    show Mdb.Desc (Mdb.conjPar e G.par) y x ↔ _
    simpa using this
  have hget : ∀ z ∈ (renG G e).chains.flatten, ∃ z0 ∈ G.chains.flatten, z = e z0 :=
    fun z hz => ⟨e.symm z, (hmem z).1 hz, by simp⟩
  refine ⟨fun x hx hp => ?_, fun x hx p sb fi d hc y hd => ?_, fun x hx p sb fi d hc y hy hp => ?_,
    fun x hx y hy hxy p sb fi fi' d d' hcx hcy => ?_, fun x hx p sb fi d hc => ?_⟩
  · obtain ⟨x0, hx0, rfl⟩ := hget x hx
    have hq := hcap x0 hx0
    rw [hq.phys] at hp; rw [hq.base, hq.top]; exact hU.reg x0 hx0 hp
  · obtain ⟨x0, hx0, rfl⟩ := hget x hx
    have hc0 := ((hcap x0 hx0).ut _ _ _ _).1 hc
    have hd0 := (hD y (e x0)).1 hd
    rw [Equiv.symm_apply_apply] at hd0
    have hy0 := (desc_mem hM hd0).1
    have hqy := hcap _ hy0
    rw [Equiv.apply_symm_apply] at hqy
    rw [hqy.phys, hqy.base, hqy.top]; exact hU.inc x0 hx0 p sb fi d hc0 _ hd0
  · obtain ⟨x0, hx0, rfl⟩ := hget x hx
    obtain ⟨y0, hy0, rfl⟩ := hget y hy
    have hq := hcap x0 hx0
    have hqy := hcap y0 hy0
    rw [hqy.phys] at hp
    rcases hU.noov x0 hx0 p sb fi d ((hq.ut _ _ _ _).1 hc) y0 hy0 hp with h | ⟨h1, h2⟩
    · left; unfold DisjR at h ⊢; rw [hqy.base, hqy.top]; exact h
    · right; rw [hqy.isUt']; refine ⟨h1, ?_⟩
      unfold Within at h2 ⊢; rw [hq.base, hq.top, hqy.base, hqy.top]; exact h2
  · obtain ⟨x0, hx0, rfl⟩ := hget x hx
    obtain ⟨y0, hy0, rfl⟩ := hget y hy
    exact hU.excl x0 hx0 y0 hy0 (fun e' => hxy (by rw [e'])) _ _ _ _ _ _
      (((hcap x0 hx0).ut _ _ _ _).1 hcx) (((hcap y0 hy0).ut _ _ _ _).1 hcy)
  · obtain ⟨x0, hx0, rfl⟩ := hget x hx
    exact hU.fib x0 hx0 _ _ _ _ (((hcap x0 hx0).ut _ _ _ _).1 hc)

/-! ## Removal (`empty_slot`) -/

theorem UtInv.remove {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    (hU : UtInv mem G) {x : U64}
    (hcap : ∀ z ∈ G.chains.flatten, z ≠ x → capV mem' z = capV mem z) :
    UtInv mem' (remG G x) := by
  have hmem : ∀ z, z ∈ (remG G x).chains.flatten ↔ z ∈ G.chains.flatten ∧ z ≠ x :=
    fun _ => Mdb.mem_removeChains hM.tree.nodup
  have hD : ∀ y z, Mdb.Desc (remG G x).par y z ↔ y ≠ x ∧ z ≠ x ∧ Mdb.Desc G.par y z :=
    Mdb.desc_remove_iff hM.no_self_par
  refine ⟨fun z hz hp => ?_, fun z hz p sb fi d hc y hd => ?_, fun z hz p sb fi d hc y hy hp => ?_,
    fun z hz y hy hzy p sb fi fi' d d' hcz hcy => ?_, fun z hz p sb fi d hc => ?_⟩
  · obtain ⟨hz0, hzx⟩ := (hmem z).1 hz
    rw [hcap z hz0 hzx] at hp ⊢; exact hU.reg z hz0 hp
  · obtain ⟨hz0, hzx⟩ := (hmem z).1 hz
    obtain ⟨hyx, -, hd0⟩ := (hD y z).1 hd
    rw [hcap z hz0 hzx] at hc
    rw [hcap y (desc_mem hM hd0).1 hyx]; exact hU.inc z hz0 p sb fi d hc y hd0
  · obtain ⟨hz0, hzx⟩ := (hmem z).1 hz
    obtain ⟨hy0, hyx⟩ := (hmem y).1 hy
    rw [hcap z hz0 hzx] at hc ⊢; rw [hcap y hy0 hyx] at hp ⊢
    exact hU.noov z hz0 p sb fi d hc y hy0 hp
  · obtain ⟨hz0, hzx⟩ := (hmem z).1 hz
    obtain ⟨hy0, hyx⟩ := (hmem y).1 hy
    rw [hcap z hz0 hzx] at hcz; rw [hcap y hy0 hyx] at hcy
    exact hU.excl z hz0 y hy0 hzy _ _ _ _ _ _ hcz hcy
  · obtain ⟨hz0, hzx⟩ := (hmem z).1 hz
    rw [hcap z hz0 hzx] at hc; exact hU.fib z hz0 _ _ _ _ hc

/-! ## Insertion of a derived cap (`insert`, with `set_untyped_cap_as_full`) -/

namespace InsCtx
variable {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} {src dest : U64} {c c1 : capability.Cap}
  (h : InsCtx th mem mem' G src dest c c1) (hU : UtInv mem G)
  (hc1 : c1 = (fullF (capV mem src) c).getD (capV mem src))
  (hutc : isUt (capV mem src) = true → c = capV mem src)
include h hU hc1 hutc

theorem co {z : U64} (hz : z ∈ G.chains.flatten) (hzs : z ≠ src) : capV mem' z = capV mem z := by
  rw [h.hcap z (h.sl hz), if_neg (h.dne hz), if_neg hzs]

/-- The source after `set_untyped_cap_as_full`, if untyped, is full. -/
theorem src_full {p sb fi : U64} {d : Bool} (hc : c1 = .Untyped p sb fi d) : fi.val = 2 ^ sb.val := by
  have hu : isUt (capV mem src) = true := by rw [← isUt_of_shape h.hsh1, hc]; rfl
  obtain ⟨q, sz, f, d0, e⟩ := isUt_iff.1 hu
  have hcc := hutc hu
  rw [hc1, hcc, e] at hc
  simp only [fullF, and_self, ↓reduceIte, Option.getD_some, capability.Cap.Untyped.injEq] at hc
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
  exact full_val (capV_ut_sb e)

/-- Each slot of the new tree, read back to a slot of the old one (`dest`
to `src`): the same range, the same untyped cap up to a larger free index. -/
theorem view {z : U64} (hz : z ∈ (insG G src dest false).chains.flatten) :
    ∃ z0 ∈ G.chains.flatten, (z = dest → z0 = src) ∧ (z ≠ dest → z0 = z) ∧
      baseF (capV mem' z) = baseF (capV mem z0) ∧ topF (capV mem' z) = topF (capV mem z0) ∧
      physF (capV mem' z) = physF (capV mem z0) ∧ isUt (capV mem' z) = isUt (capV mem z0) ∧
      ∀ p sb fi d, capV mem' z = .Untyped p sb fi d → ∃ fi0, capV mem z0 = .Untyped p sb fi0 d ∧ fi0.val ≤ fi.val := by
  rcases (h.memI false z).1 hz with rfl | hz0
  · have hq := UtEq.of_shape h.hsh hutc
    refine ⟨src, h.hsrc, fun _ => rfl, fun e => absurd rfl e, ?_⟩
    rw [h.cd]
    refine ⟨hq.base, hq.top, hq.phys, hq.isUt', fun p sb fi d e => ⟨fi, (hq.ut _ _ _ _).1 e, le_refl _⟩⟩
  · by_cases hzs : z = src
    · subst hzs
      obtain ⟨e1, e2, e3⟩ := range_of_shape h.hsh1
      refine ⟨z, hz0, fun e => absurd e (h.dne hz0), fun _ => rfl, ?_⟩
      rw [h.cs]
      refine ⟨e1, e2, e3, isUt_of_shape h.hsh1, fun p sb fi d e => ?_⟩
      have hf := h.src_full hU hc1 hutc e
      have hu : isUt (capV mem z) = true := by rw [← isUt_of_shape h.hsh1, e]; rfl
      obtain ⟨q, sz, f, d0, e0⟩ := isUt_iff.1 hu
      have hcc := hutc hu
      rw [hc1, hcc, e0] at e
      simp only [fullF, and_self, ↓reduceIte, Option.getD_some, capability.Cap.Untyped.injEq] at e
      obtain ⟨rfl, rfl, -, rfl⟩ := e
      exact ⟨f, e0, by rw [hf]; exact hU.fib z hz0 _ _ _ _ e0⟩
    · refine ⟨z, hz0, fun e => absurd e (h.dne hz0), fun _ => rfl, ?_⟩
      rw [h.co hU hc1 hutc hz0 hzs]
      exact ⟨rfl, rfl, rfl, rfl, fun p sb fi d e => ⟨fi, e, le_refl _⟩⟩

theorem memI' (b : Bool) {z : U64} (hz : z ∈ (insG G src dest b).chains.flatten) :
    z ∈ (insG G src dest false).chains.flatten := (h.memI false z).2 ((h.memI b z).1 hz)

/-- **Inserting a derived cap keeps `UtInv`** (whatever `dest`'s parent). -/
theorem utinv (b : Bool) : UtInv mem' (insG G src dest b) := by
  have V := fun {z : U64} (hz : z ∈ (insG G src dest b).chains.flatten) => h.view hU hc1 hutc (h.memI' hU hc1 hutc b hz)
  refine ⟨fun x hx hp => ?_, fun x hx p sb fi d hc y hd => ?_, fun x hx p sb fi d hc y hy hp => ?_,
    fun x hx y hy hxy p sb fi fi' d d' hcx hcy => ?_, fun x hx p sb fi d hc => ?_⟩
  · obtain ⟨x0, hx0, -, -, e1, e2, e3, -, -⟩ := V hx
    rw [e3] at hp; rw [e1, e2]; exact hU.reg x0 hx0 hp
  · have hy : y ∈ (insG G src dest b).chains.flatten := by
      have := (h.desc b y x).1 hd
      rcases this with hd0 | ⟨rfl, -⟩
      · exact (h.memI b y).2 (Or.inr (desc_mem h.hM hd0).1)
      · exact (h.memI b _).2 (Or.inl rfl)
    obtain ⟨y0, hy0, hyd, hyn, f1, f2, f3, -, -⟩ := V hy
    rcases (h.desc b y x).1 hd with hd0 | ⟨rfl, hxs⟩
    · obtain ⟨hy0', hx0'⟩ := desc_mem h.hM hd0
      obtain ⟨x0, -, -, hxn, -, -, -, -, hu⟩ := V hx
      have hx0e := hxn (h.dne hx0')
      have hy0e := hyn (h.dne hy0')
      subst hx0e hy0e
      obtain ⟨fi0, hc0, hle⟩ := hu p sb fi d hc
      obtain ⟨g1, g2, g3⟩ := hU.inc x0 hx0' p sb fi0 d hc0 y0 hd0
      rw [f1, f2, f3]; exact ⟨g1, g2, by omega⟩
    · have ys := hyd rfl; rw [ys] at f1 f2 f3
      rcases hxs with ⟨-, rfl⟩ | hd0
      · rw [h.cs] at hc
        have hf := h.src_full hU hc1 hutc hc
        have hu : isUt (capV mem x) = true := by rw [← isUt_of_shape h.hsh1, hc]; rfl
        obtain ⟨q, sz, f, d0, e0⟩ := isUt_iff.1 hu
        have hcc := hutc hu
        rw [hc1, hcc, e0] at hc
        simp only [fullF, and_self, ↓reduceIte, Option.getD_some, capability.Cap.Untyped.injEq] at hc
        obtain ⟨rfl, rfl, -, rfl⟩ := hc
        have hr := hU.reg x h.hsrc (by rw [e0]; exact physF_ut _ _ _ _)
        rw [e0] at hr
        obtain ⟨r1, r2, -⟩ := ut_range (capV_ut_sb e0) hr
        rw [f1, f2, f3, e0, r1, r2, physF_ut]
        have := Nat.one_le_two_pow (n := sz.val)
        exact ⟨rfl, le_refl _, by omega⟩
      · have hx0' := (desc_mem h.hM hd0).2
        obtain ⟨x0, -, -, hxn, -, -, -, -, hu⟩ := V hx
        have hx0e := hxn (h.dne hx0'); subst hx0e
        obtain ⟨fi0, hc0, hle⟩ := hu p sb fi d hc
        obtain ⟨g1, g2, g3⟩ := hU.inc x0 hx0' p sb fi0 d hc0 src hd0
        rw [f1, f2, f3]; exact ⟨g1, g2, by omega⟩
  · obtain ⟨x0, hx0, -, -, e1, e2, -, -, hu⟩ := V hx
    obtain ⟨y0, hy0, -, -, f1, f2, f3, f4, -⟩ := V hy
    obtain ⟨fi0, hc0, hle⟩ := hu p sb fi d hc
    rw [f3] at hp
    rcases hU.noov x0 hx0 p sb fi0 d hc0 y0 hy0 hp with g | ⟨g1, g2⟩
    · left; unfold DisjR at g ⊢; rw [f1, f2]; omega
    · right; rw [f4]; refine ⟨g1, ?_⟩
      unfold Within at g2 ⊢; rw [e1, e2, f1, f2]; exact g2
  · obtain ⟨x0, hx0, hxd, hxn, -, -, -, -, hu⟩ := V hx
    obtain ⟨y0, hy0, hyd, hyn, -, -, -, -, hv⟩ := V hy
    obtain ⟨g0, hg0, hgle⟩ := hu p sb fi d hcx
    obtain ⟨g0', hg0', hgle'⟩ := hv p sb fi' d' hcy
    by_cases hxy0 : x0 = y0
    · -- one of them is `src`, now full
      have : x = src ∨ y = src := by
        by_cases hx' : x = dest
        · have := hxd hx'
          by_cases hy' : y = dest
          · exact absurd (hx'.trans hy'.symm) hxy
          · right; rw [← hyn hy', ← hxy0, this]
        · left; rw [← hxn hx']
          by_cases hy' : y = dest
          · rw [hxy0, hyd hy']
          · exact absurd ((hxn hx').symm.trans (hxy0.trans (hyn hy'))) hxy
      rcases this with rfl | rfl
      · rw [h.cs] at hcx; exact Or.inl (le_of_eq (h.src_full hU hc1 hutc hcx).symm)
      · rw [h.cs] at hcy; exact Or.inr (le_of_eq (h.src_full hU hc1 hutc hcy).symm)
    · rcases hU.excl x0 hx0 y0 hy0 hxy0 _ _ _ _ _ _ hg0 hg0' with g | g
      · left; omega
      · right; omega
  · obtain ⟨x0, hx0, -, hxn, -, -, -, -, hu⟩ := V hx
    obtain ⟨fi0, hc0, hle⟩ := hu p sb fi d hc
    by_cases hxs : x = src
    · subst hxs; rw [h.cs] at hc; exact le_of_eq (h.src_full hU hc1 hutc hc)
    · by_cases hxd : x = dest
      · subst hxd; rw [h.cd] at hc
        have hq := UtEq.of_shape h.hsh hutc
        exact hU.fib _ h.hsrc _ _ _ _ ((hq.ut _ _ _ _).1 hc)
      · have := hxn hxd; subst this
        rw [h.co hU hc1 hutc hx0 hxs] at hc; exact hU.fib _ hx0 _ _ _ _ hc

end InsCtx

/-! ## FL4's functions -/

section
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`cdt::insert` of a derived cap keeps `UtInv`**, for a cap of the
source's shape, equal to it if untyped (FL4's `derive_cap` and
`update_cap_data` return an untyped cap unchanged). -/
theorem insert_utinv (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    (hI : MdbInv (L.mem s) G) (hU : UtInv (L.mem s) G) {src dest : U64} (hsrc : src ∈ G.chains.flatten)
    (hd : IsSlot th dest) (hdest : dest ∉ G.chains.flatten) {srcC : capability.Cap}
    (hsrcC : capAt (L.mem s) src = ok srcC)
    (c : capability.Cap) (he : EncWf c) (hsh : shape c = shape srcC)
    (hbd : badgeF c = badgeF srcC ∨ badgeF srcC = 0#u64)
    (hut : isUt srcC = true → ∀ y, ¬ Mdb.Desc G.par y src) (hzb : isZb srcC = false)
    (hutc : isUt srcC = true → c = srcC) (b : Bool) :
    cdt.insert st s c src dest ⦃ s' => UtInv (L.mem s') (insG G src dest b) ⦄ := by
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hs := hslot src hsrc
  have hne : src ≠ dest := fun e => hdest (e ▸ hsrc)
  have hes : EncWf srcC := by rw [capAt_words] at hsrcC; exact decode_encWf hsrcC
  have hcv := capV_of_capAt hsrcC
  have hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src) := by
    rcases hM.next_mem hsrc with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, fun e => hdest (e ▸ h1), h2⟩
  have hNc : Canonical (nextOf (L.mem s) src) := by
    rcases hnx with h | ⟨h, -, -⟩
    · rw [h]; exact canonical_zero
    · exact h.canonical hP
  apply WP.spec_mono (insert_mem hP s c src dest hs hd hne srcC hsrcC hnx)
  intro s' hW
  have hctx : InsCtx th (L.mem s) (L.mem s') G src dest c ((fullF srcC c).getD srcC) :=
    { hM := hM, hI := hI, hsrc := hsrc, hd := hd, hdest := hdest
      hnext := fun a ha => hW.nextOf' hP ha hd hne hNc
      hcap := fun a ha => by
        have := hW.capAt' ha he hes hsrcC
        rw [capAt_capV] at this
        by_cases h1 : a = dest
        · subst h1; simp only [↓reduceIte] at this ⊢; simpa using this
        · by_cases h2 : a = src
          · subst h2; simp only [h1, ↓reduceIte] at this ⊢; simpa using this
          · simp only [h1, h2, ↓reduceIte] at this ⊢; rw [capAt_capV] at this; simpa using this
      hrev := fun a ha => by rw [hW.revOf' ha hne, hcv]
      hfb := fun a ha => by rw [hW.fbOf' ha hne, hcv]
      hsh := by rw [hcv]; exact hsh
      hbd := by rw [hcv]; exact hbd
      hsh1 := by rw [hcv]; exact (fullF_shape srcC c).1
      hbd1 := by rw [hcv]; exact (fullF_shape srcC c).2
      hut := by rw [hcv]; exact hut
      hzb := by rw [hcv]; exact hzb }
  exact hctx.utinv hU (by rw [hcv]) (by rw [hcv]; exact hutc) b

/-- **`cdt::move_cap` keeps `UtInv`**, for a new cap of the old one's
shape, equal to it if untyped. -/
theorem move_utinv (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    (hU : UtInv (L.mem s) G) {src dest : U64} (hsrcm : src ∈ G.chains.flatten) (hd : IsSlot th dest)
    (hdestm : dest ∉ G.chains.flatten) {srcC : capability.Cap} (hsrcC : capAt (L.mem s) src = ok srcC)
    (c : capability.Cap) (he : EncWf c) (hsh : shape c = shape srcC) (hutc : isUt srcC = true → c = srcC) :
    cdt.move_cap st s c src dest ⦃ s' => UtInv (L.mem s') (renG G (Equiv.swap src dest)) ⦄ := by
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hs := hslot src hsrcm
  have hne : src ≠ dest := fun e => hdestm (e ▸ hsrcm)
  have hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src) := by
    rcases hM.next_mem hsrcm with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, fun e => hdestm (e ▸ h1), h2⟩
  have hpv : prevOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (prevOf (L.mem s) src) ∧ prevOf (L.mem s) src ≠ dest ∧ prevOf (L.mem s) src ≠ src) := by
    by_cases h0 : prevOf (L.mem s) src = 0#u64
    · exact Or.inl h0
    · obtain ⟨h1, h2⟩ := hM.prev_link hsrcm h0
      refine Or.inr ⟨hslot _ h1, fun e => hdestm (e ▸ h1), fun e => ?_⟩
      rw [e] at h2
      rcases hM.next_mem hsrcm with h | ⟨-, h⟩
      · rw [h] at h2; exact hs.ne_zero hP h2.symm
      · exact h h2
  apply WP.spec_mono (move_mem hP s c _ _ hs hd hne hpv hnx)
  intro s' hW
  have hcv := capV_of_capAt hsrcC
  have hdne : ∀ a, a ∈ G.chains.flatten → a ≠ dest := fun a h e => hdestm (e ▸ h)
  refine UtInv.rename hM hU _ (fun a ha => ?_)
  by_cases has : a = src
  · rw [has, Equiv.swap_apply_left, capV_of_capAt (c := c) (by rw [hW.capAt' hd he hne]; simp), hcv]
    exact UtEq.of_shape hsh hutc
  · rw [Equiv.swap_apply_of_ne_of_ne has (hdne a ha)]
    have := hW.capAt' (hslot a ha) he hne
    rw [if_neg (hdne a ha), if_neg has, capAt_capV, capAt_capV] at this
    simp at this; rw [this]; exact UtEq.refl _

/-- **`cdt::swap` keeps `UtInv`**, for new caps of the old ones' shapes,
equal to them if untyped. -/
theorem swap_utinv (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    (hU : UtInv (L.mem s) G) {s1 s2 : U64} (hm1 : s1 ∈ G.chains.flatten) (hm2 : s2 ∈ G.chains.flatten)
    (hne : s1 ≠ s2) (c1 c2 : capability.Cap) (he1 : EncWf c1) (he2 : EncWf c2)
    (hsh1 : shape c1 = shape (capV (L.mem s) s1)) (hut1 : isUt (capV (L.mem s) s1) = true → c1 = capV (L.mem s) s1)
    (hsh2 : shape c2 = shape (capV (L.mem s) s2)) (hut2 : isUt (capV (L.mem s) s2) = true → c2 = capV (L.mem s) s2) :
    cdt.swap st s c1 s1 c2 s2 ⦃ s' => UtInv (L.mem s') (renG G (Equiv.swap s1 s2)) ⦄ := by
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hNx : ∀ a, a ∈ G.chains.flatten → nextOf (L.mem s) a = 0#u64 ∨ IsSlot th (nextOf (L.mem s) a) := by
    intro a ha; rcases hM.next_mem ha with h | ⟨h, -⟩ <;> [exact Or.inl h; exact Or.inr (hslot _ h)]
  have hPx : ∀ a, a ∈ G.chains.flatten → prevOf (L.mem s) a = 0#u64 ∨ IsSlot th (prevOf (L.mem s) a) := by
    intro a ha; by_cases h : prevOf (L.mem s) a = 0#u64
    · exact Or.inl h
    · exact Or.inr (hslot _ (hM.prev_link ha h).1)
  apply WP.spec_mono (swap_fields hP s c1 c2 _ _ (hslot _ hm1) (hslot _ hm2) hne he1 he2 (hPx _ hm1) (hNx _ hm1)
    (hPx _ hm2) (hNx _ hm2))
  intro s' hW
  refine UtInv.rename hM hU _ (fun a ha => ?_)
  by_cases e1 : a = s1
  · have h := (hW _ (hslot _ hm2)).1
    rw [capAt_capV, if_pos rfl] at h
    rw [e1, Equiv.swap_apply_left]; simp at h; rw [h]; exact UtEq.of_shape hsh1 hut1
  · by_cases e2 : a = s2
    · have h := (hW _ (hslot _ hm1)).1
      rw [capAt_capV, if_neg hne, if_pos rfl] at h
      rw [e2, Equiv.swap_apply_right]; simp at h; rw [h]; exact UtEq.of_shape hsh2 hut2
    · have h := (hW _ (hslot _ ha)).1
      rw [capAt_capV, if_neg e2, if_neg e1, capAt_capV] at h
      rw [Equiv.swap_apply_of_ne_of_ne e1 e2]; simp at h; rw [h]; exact UtEq.refl _

end

section
variable {S A : Type} {st : machine.Store S} [L : P1.LawfulStore st] {ar : machine.Arch A}

/-- **`cdt::empty_slot` keeps `UtInv`.** -/
theorem empty_slot_utinv {th : TypedHeap} (hP : Placed th) (s : S) (a : A) (G : MdbGhost)
    (hM : MdbLinks th (L.mem s) G) (hU : UtInv (L.mem s) G) {x : U64} (hxm : x ∈ G.chains.flatten)
    {c : capability.Cap} (hc : capAt (L.mem s) x = ok c) (hcn : c ≠ .Null) :
    cdt.empty_slot st ar s a x .Null ⦃ r => UtInv (L.mem r.1) (remG G x) ⦄ := by
  have hslot : ∀ y, y ∈ G.chains.flatten → IsSlot th y := fun y h => ((hM.members y).1 h).1
  have hx := hslot x hxm
  have hnx : nextOf (L.mem s) x = 0#u64 ∨ (IsSlot th (nextOf (L.mem s) x) ∧ nextOf (L.mem s) x ≠ x) := by
    rcases hM.next_mem hxm with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, h2⟩
  have hpv : prevOf (L.mem s) x = 0#u64 ∨ (IsSlot th (prevOf (L.mem s) x) ∧ prevOf (L.mem s) x ≠ x) := by
    by_cases h0 : prevOf (L.mem s) x = 0#u64
    · exact Or.inl h0
    · obtain ⟨h1, h2⟩ := hM.prev_link hxm h0
      refine Or.inr ⟨hslot _ h1, fun e => ?_⟩
      rw [e] at h2
      rcases hM.next_mem hxm with h | ⟨-, h⟩
      · rw [h] at h2; exact hx.ne_zero hP h2.symm
      · exact h h2
  have hPN := hM.prev_ne_next hP hxm
  apply WP.spec_mono (empty_slot_mem hP s a _ hx c hc hcn hpv hnx hPN)
  rintro r ⟨hW, -⟩
  refine UtInv.remove hM hU (fun y hy hyx => ?_)
  have := hW.capAt' (hslot y hy); rw [if_neg hyx, capAt_capV, capAt_capV] at this; simpa using this

end

end

end Fl4Proofs.P3
