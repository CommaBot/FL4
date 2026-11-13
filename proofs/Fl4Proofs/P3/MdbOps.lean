/-
P3 (DESIGN.md §9), CSpace: `MdbInv` is kept by FL4's `cdt::insert` (of a
derived cap), `cdt::move_cap`, `cdt::swap` and `cdt::empty_slot`, read off
the word-level descriptions of those functions (`InsWords`, `MovWords`,
`SwapFields`, `EmpWords`).
-/
import Fl4Proofs.P3.MdbInvRen
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

theorem fullF_shape (srcC c : capability.Cap) :
    shape ((fullF srcC c).getD srcC) = shape srcC ∧ badgeF ((fullF srcC c).getD srcC) = badgeF srcC := by
  cases srcC <;> cases c <;> simp [fullF] <;> split <;> simp_all [shape, badgeF]

theorem capV_of_capAt {mem : U64 → U64} {a : U64} {c : capability.Cap} (h : capAt mem a = ok c) :
    capV mem a = c := by
  rw [capAt_capV] at h; simpa using h

section
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem InsWords.fbOf' {s s' : S} {c srcC : capability.Cap} {src dest : U64}
    (hW : InsWords (L := L) th s s' c srcC src dest) {a : U64} (ha : IsSlot th a) (hne : src ≠ dest) :
    fbOf (L.mem s') a = if a = dest then revF c srcC else fbOf (L.mem s) a := by
  rw [show fbOf (L.mem s') a = (L.mem s' (wordOf a 24#u64)).bv.getLsbD 49 from rfl, hW a ha _ off24]
  by_cases h1 : a = dest
  · simp only [h1, ↓reduceIte, lit_ne]
    show (setBitF (setBitF _ 48 _) 49 _).getLsbD 49 = _
    rw [getLsbD_setBitF _ _ _ (Or.inr rfl) (Or.inr rfl)]
    simp
  · by_cases h2 : a = src
    · subst h2
      simp only [h1, ↓reduceIte]
      show (setNextF _ _).getLsbD 49 = _
      rw [getLsbD_setNextF _ _ 49 (by decide) (by decide)]; rfl
    · simp only [h1, h2, ↓reduceIte, lit_ne, and_false]; rfl

/-- **`cdt::insert` of a derived cap keeps `MdbInv`**, with the ghost tree
grown as FL4's parent test from `src` says. -/
theorem insert_mdbinv (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    (hI : MdbInv (L.mem s) G) {src dest : U64} (hsrc : src ∈ G.chains.flatten) (hd : IsSlot th dest)
    (hdest : dest ∉ G.chains.flatten) {srcC : capability.Cap} (hsrcC : capAt (L.mem s) src = ok srcC)
    (c : capability.Cap) (he : EncWf c) (hsh : shape c = shape srcC)
    (hbd : badgeF c = badgeF srcC ∨ badgeF srcC = 0#u64)
    (hut : isUt srcC = true → ∀ y, ¬ Mdb.Desc G.par y src) (hzb : isZb srcC = false) :
    cdt.insert st s c src dest ⦃ s' =>
      MdbInv (L.mem s') (insG G src dest (isPF (revOf (L.mem s) src) srcC c (revF c srcC))) ⦄ := by
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
  have hNs : nextOf (L.mem s) src ≠ src := by
    rcases hnx with h | ⟨-, -, h⟩
    · rw [h]; exact (hs.ne_zero hP).symm
    · exact h
  have hNc : Canonical (nextOf (L.mem s) src) := by
    rcases hnx with h | ⟨h, -, -⟩
    · rw [h]; exact canonical_zero
    · exact h.canonical hP
  apply WP.spec_mono (insert_mem hP s c src dest hs hd hne srcC hsrcC hnx)
  intro s' hW
  have := InsCtx.inv (c := c) (c1 := (fullF srcC c).getD srcC) (th := th) (mem := L.mem s) (mem' := L.mem s')
    (G := G) (src := src) (dest := dest)
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
  rw [hcv] at this
  exact this

end

section
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem EmpWords.fbOf' {s s' : S} {xs : U64} (hW : EmpWords (L := L) th s s' xs) {a : U64} (ha : IsSlot th a)
    (hPN : prevOf (L.mem s) xs ≠ 0#u64 → nextOf (L.mem s) xs ≠ 0#u64 → prevOf (L.mem s) xs ≠ nextOf (L.mem s) xs) :
    fbOf (L.mem s') a = if a = xs then false
      else if nextOf (L.mem s) xs ≠ 0#u64 ∧ a = nextOf (L.mem s) xs then (fbOf (L.mem s) a || fbOf (L.mem s) xs)
      else fbOf (L.mem s) a := by
  rw [show fbOf (L.mem s') a = (L.mem s' (wordOf a 24#u64)).bv.getLsbD 49 from rfl, hW a ha _ off24]
  by_cases h1 : a = xs
  · simp [h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h3 : prevOf (L.mem s) xs ≠ 0#u64 ∧ a = prevOf (L.mem s) xs
    · rw [if_pos ⟨h3.1, h3.2, rfl⟩]
      have h5 : ¬ (nextOf (L.mem s) xs ≠ 0#u64 ∧ a = nextOf (L.mem s) xs) := by
        rintro ⟨hn, e⟩; exact hPN h3.1 hn (h3.2 ▸ e)
      rw [if_neg h5]
      show (setNextF _ _).getLsbD 49 = _
      rw [getLsbD_setNextF _ _ 49 (by decide) (by decide)]; rfl
    · rw [if_neg (fun h => h3 ⟨h.1, h.2.1⟩)]
      have h4 : ¬ (nextOf (L.mem s) xs ≠ 0#u64 ∧ a = nextOf (L.mem s) xs ∧ (24#u64 : U64) = 16#u64) := by
        rintro ⟨-, -, h⟩; exact absurd h (by decide)
      rw [if_neg h4]
      by_cases h5 : nextOf (L.mem s) xs ≠ 0#u64 ∧ a = nextOf (L.mem s) xs
      · rw [if_pos ⟨h5.1, h5.2, rfl⟩, if_pos h5]
        show (setBitF _ 49 _).getLsbD 49 = _
        rw [getLsbD_setBitF _ _ _ (Or.inr rfl) (Or.inr rfl)]; simp
      · rw [if_neg (fun h => h5 ⟨h.1, h.2.1⟩), if_neg h5]; rfl

end

section
variable {S A : Type} {st : machine.Store S} [L : P1.LawfulStore st] {ar : machine.Arch A}

/-- **`cdt::empty_slot` keeps `MdbInv`.** -/
theorem empty_slot_mdbinv {th : TypedHeap} (hP : Placed th) (s : S) (a : A) (G : MdbGhost)
    (hM : MdbLinks th (L.mem s) G) (hI : MdbInv (L.mem s) G) {x : U64} (hxm : x ∈ G.chains.flatten)
    {c : capability.Cap} (hc : capAt (L.mem s) x = ok c) (hcn : c ≠ .Null) :
    cdt.empty_slot st ar s a x .Null ⦃ r => MdbInv (L.mem r.1) (remG G x) ⦄ := by
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
  have hNc : Canonical (nextOf (L.mem s) x) := by
    rcases hnx with h | ⟨h, -⟩
    · rw [h]; exact canonical_zero
    · exact h.canonical hP
  apply WP.spec_mono (empty_slot_mem hP s a _ hx c hc hcn hpv hnx hPN)
  rintro r ⟨hW, -⟩
  refine EmpCtx.inv (th := th) ⟨hP, hM, hI, hxm, fun y hy hyx => ?_, fun y hy hyx => ?_, fun y hy hyx => ?_,
    fun y hy hyx => ?_⟩
  · have := hW.capAt' hy; rw [if_neg hyx, capAt_capV, capAt_capV] at this; simpa using this
  · rw [hW.revOf' hy, if_neg hyx]
  · rw [hW.fbOf' hy hPN, if_neg hyx]
  · rw [hW.nextOf' hy hNc hPN, if_neg hyx]

end

section
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem MovWords.fbOf' {s s' : S} {c : capability.Cap} {src dest : U64}
    (hW : MovWords (L := L) th s s' c src dest) {a : U64} (ha : IsSlot th a) :
    fbOf (L.mem s') a = if a = dest then fbOf (L.mem s) src else if a = src then false else fbOf (L.mem s) a := by
  rw [show fbOf (L.mem s') a = (L.mem s' (wordOf a 24#u64)).bv.getLsbD 49 from rfl, hW a ha _ off24]
  by_cases h1 : a = dest
  · rw [if_pos h1, if_pos h1, if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    show (setBitF (setBitF _ 48 _) 49 _).getLsbD 49 = _
    rw [getLsbD_setBitF _ _ _ (Or.inr rfl) (Or.inr rfl)]
    simp
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : a = src
    · rw [if_pos h2, if_pos h2]; rfl
    · rw [if_neg h2, if_neg h2]
      by_cases h3 : prevOf (L.mem s) src ≠ 0#u64 ∧ a = prevOf (L.mem s) src ∧ (24#u64 : U64) = 24#u64
      · rw [if_pos h3]
        show (setNextF _ _).getLsbD 49 = _
        rw [getLsbD_setNextF _ _ 49 (by decide) (by decide)]; rfl
      · rw [if_neg h3]
        have h4 : ¬ (nextOf (L.mem s) src ≠ 0#u64 ∧ a = nextOf (L.mem s) src ∧ (24#u64 : U64) = 16#u64) := by
          rintro ⟨-, -, h⟩; exact absurd h (by decide)
        rw [if_neg h4]; rfl

/-- **`cdt::move_cap` keeps `MdbInv`**, for a new cap of the old one's shape
and badge. -/
theorem move_mdbinv (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    (hI : MdbInv (L.mem s) G) {src dest : U64} (hsrcm : src ∈ G.chains.flatten) (hd : IsSlot th dest)
    (hdestm : dest ∉ G.chains.flatten) {srcC : capability.Cap} (hsrcC : capAt (L.mem s) src = ok srcC)
    (c : capability.Cap) (he : EncWf c) (hcnn : c ≠ .Null) (hsh : shape c = shape srcC)
    (hbd : badgeF c = badgeF srcC) :
    cdt.move_cap st s c src dest ⦃ s' => MdbInv (L.mem s') (renG G (Equiv.swap src dest)) ⦄ := by
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
  have hNc : Canonical (nextOf (L.mem s) src) := by
    rcases hnx with h | ⟨h, -, -⟩
    · rw [h]; exact canonical_zero
    · exact h.canonical hP
  apply WP.spec_mono (move_mem hP s c _ _ hs hd hne hpv hnx)
  intro s' hW
  have hRL : RenLinks th (L.mem s) (L.mem s') (Equiv.swap src dest) G := by
    refine RenLinks.move hP hM hsrcm hd hdestm (fun x hx => hW.prevOf' hx hne)
      (fun x hx => hW.nextOf' hP hx hd hne hNc) ?_ ?_ ⟨c, ?_, hcnn⟩
    · intro x hx h1 h2; rw [hW.capAt' hx he hne]; simp [h1, h2]
    · rw [hW.capAt' hs he hne]; simp [hne]
    · rw [hW.capAt' hd he hne]; simp
  have hcv := capV_of_capAt hsrcC
  have hdne : ∀ a, a ∈ G.chains.flatten → a ≠ dest := fun a h e => hdestm (e ▸ h)
  refine MdbInv.rename hM hI _ hRL.e0 hRL.next (fun a ha => ?_) (fun a ha => ?_) (fun a ha => ?_)
  · by_cases has : a = src
    · rw [has, Equiv.swap_apply_left, capV_of_capAt (c := c) (by rw [hW.capAt' hd he hne]; simp), hcv]
      exact ⟨hsh, hbd⟩
    · rw [Equiv.swap_apply_of_ne_of_ne has (hdne a ha)]
      have := hW.capAt' (hslot a ha) he hne
      rw [if_neg (hdne a ha), if_neg has, capAt_capV, capAt_capV] at this
      simp at this; rw [this]; exact ⟨rfl, rfl⟩
  · by_cases has : a = src
    · rw [has, Equiv.swap_apply_left, hW.revOf' hd hne, if_pos rfl]
    · rw [Equiv.swap_apply_of_ne_of_ne has (hdne a ha), hW.revOf' (hslot a ha) hne, if_neg (hdne a ha),
        if_neg has]
  · by_cases has : a = src
    · rw [has, Equiv.swap_apply_left, hW.fbOf' hd, if_pos rfl]
    · rw [Equiv.swap_apply_of_ne_of_ne has (hdne a ha), hW.fbOf' (hslot a ha), if_neg (hdne a ha), if_neg has]

/-- **`cdt::swap` keeps `MdbInv`**, for new caps of the old ones' shapes
and badges. -/
theorem swap_mdbinv (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    (hI : MdbInv (L.mem s) G) {s1 s2 : U64} (hm1 : s1 ∈ G.chains.flatten) (hm2 : s2 ∈ G.chains.flatten)
    (hne : s1 ≠ s2) (c1 c2 : capability.Cap) (he1 : EncWf c1) (he2 : EncWf c2)
    (hcn1 : c1 ≠ .Null) (hcn2 : c2 ≠ .Null)
    (hsh1 : shape c1 = shape (capV (L.mem s) s1)) (hbd1 : badgeF c1 = badgeF (capV (L.mem s) s1))
    (hsh2 : shape c2 = shape (capV (L.mem s) s2)) (hbd2 : badgeF c2 = badgeF (capV (L.mem s) s2)) :
    cdt.swap st s c1 s1 c2 s2 ⦃ s' => MdbInv (L.mem s') (renG G (Equiv.swap s1 s2)) ⦄ := by
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
  have hRL := RenLinks.swap hP hM hm1 hm2 hne hcn1 hcn2
    (fun x hx => ⟨(hW x hx).1, (hW x hx).2.1, (hW x hx).2.2.1⟩)
  refine MdbInv.rename hM hI _ hRL.e0 hRL.next (fun a ha => ?_) (fun a ha => ?_) (fun a ha => ?_)
  · by_cases e1 : a = s1
    · have h := (hW _ (hslot _ hm2)).1
      rw [capAt_capV, if_pos rfl] at h
      rw [e1, Equiv.swap_apply_left]; simp at h; rw [h]; exact ⟨hsh1, hbd1⟩
    · by_cases e2 : a = s2
      · have h := (hW _ (hslot _ hm1)).1
        rw [capAt_capV, if_neg hne, if_pos rfl] at h
        rw [e2, Equiv.swap_apply_right]; simp at h; rw [h]; exact ⟨hsh2, hbd2⟩
      · have h := (hW _ (hslot _ ha)).1
        rw [capAt_capV, if_neg e2, if_neg e1, capAt_capV] at h
        rw [Equiv.swap_apply_of_ne_of_ne e1 e2]; simp at h; rw [h]; exact ⟨rfl, rfl⟩
  · by_cases e1 : a = s1
    · rw [e1, Equiv.swap_apply_left, (hW _ (hslot _ hm2)).2.2.2.1, if_pos rfl]
    · by_cases e2 : a = s2
      · rw [e2, Equiv.swap_apply_right, (hW _ (hslot _ hm1)).2.2.2.1, if_neg hne, if_pos rfl]
      · rw [Equiv.swap_apply_of_ne_of_ne e1 e2, (hW _ (hslot _ ha)).2.2.2.1, if_neg e2, if_neg e1]
  · by_cases e1 : a = s1
    · rw [e1, Equiv.swap_apply_left, (hW _ (hslot _ hm2)).2.2.2.2, if_pos rfl]
    · by_cases e2 : a = s2
      · rw [e2, Equiv.swap_apply_right, (hW _ (hslot _ hm1)).2.2.2.2, if_neg hne, if_pos rfl]
      · rw [Equiv.swap_apply_of_ne_of_ne e1 e2, (hW _ (hslot _ ha)).2.2.2.2, if_neg e2, if_neg e1]

end

end

end Fl4Proofs.P3
