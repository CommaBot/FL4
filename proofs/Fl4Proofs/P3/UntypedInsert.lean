/-
P3 (DESIGN.md §9), untyped: **`cdt::insert_new_cap`** (seL4
`insertNewCap`), which links a new cap's slot right after its parent (the
untyped cap's slot) with the revocable and first-badged bits set, against
l4v `create_cap` (set the CDT parent to the untyped's slot, mark the slot
original, set the cap).

* `insert_new_mem`: every word of every slot afterwards (`InsNWords`), and
  the cap, links and bits of each slot read off them;
* `insert_new_refines`: the state relation (`StateRel`, `SlotsValid`),
  `MdbLinks` with the ghost tree grown by `dest` as a child of `src`
  (`insG … true`), and `CdtRel`, against the spec's single outcome of
  `create_cap`.
-/
import Fl4Proofs.P3.UntypedRetype
import Fl4Proofs.P3.MdbOps
import Fl4Proofs.P3.InsertRefine
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section
set_option linter.unusedSimpArgs false

section InsertNewMem
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

attribute [local step] set_cap_spec

/-- The slot words after `cdt::insert_new_cap s src dest c`. -/
def InsNWords (th : TypedHeap) (s s' : S) (c : capability.Cap) (src dest : U64) : Prop :=
  ∀ a, IsSlot th a → ∀ k, Off k →
    L.mem s' (wordOf a k) =
      if a = dest then
        (if k = 0#u64 then ⟨(encodeF c).1⟩ else if k = 8#u64 then ⟨(encodeF c).2⟩ else
         if k = 16#u64 then src else
         ⟨setBitF (setBitF (setNextF (L.mem s (wordOf dest 24#u64)).bv (nextOf (L.mem s) src).bv) 48 true) 49 true⟩)
      else if a = src then
        (if k = 24#u64 then ⟨setNextF (L.mem s (wordOf src 24#u64)).bv dest.bv⟩ else L.mem s (wordOf a k))
      else if nextOf (L.mem s) src ≠ 0#u64 ∧ a = nextOf (L.mem s) src ∧ k = 16#u64 then dest
      else L.mem s (wordOf a k)

set_option maxRecDepth 8000 in
/-- What `cdt::insert_new_cap` does to the slots, word by word. -/
theorem insert_new_mem (hP : Placed th) (s : S) (c : capability.Cap) (src dest : U64)
    (hs : IsSlot th src) (hd : IsSlot th dest) (hne : src ≠ dest)
    (hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src)) :
    cdt.insert_new_cap st s src dest c ⦃ s' => InsNWords (L := L) th s s' c src dest ⦄ := by
  unfold cdt.insert_new_cap
  step; step; step; step; step; step
  simp only [obj.Slot.is_null, bind_ok]
  subst next_post
  by_cases hz0 : nextOf (L.mem s) src = 0#u64
  · simp only [hz0, decide_true, ↓reduceIte, bind_ok]
    step*
    unfold InsNWords
    intro a ha k hk
    have e2 : ∀ s1 : S, L.wr (L.wr s1 dest ⟨(encodeF c).1⟩) (core.num.U64.wrapping_add dest 8#u64) ⟨(encodeF c).2⟩ =
        wrCap (L := L) s1 dest c := fun _ => rfl
    subst_vars
    try rw [e2]
    have hz : nextOf (L.mem s) src = 0#u64 := hz0
    have hne' := Ne.symm hne
    clear * - hP ha hs hd hne hne' hz hk
    simp only [wrCap_eq] <;>
      simp only [mem_wr_slot hP, ha, hs, hd, hk, off0, off8, off16, off24, hz, ne_eq, not_true_eq_false,
        false_and, ↓reduceIte] <;>
      rcases hk with rfl | rfl | rfl | rfl <;> by_cases h1 : a = dest <;> by_cases h2 : a = src <;>
      (try subst h1) <;> (try subst h2) <;>
      first
      | exact absurd rfl hne
      | simp only [lit_ne, true_and, and_true, and_false, false_and, ↓reduceIte, and_self,
          not_false_eq_true, *]
  · simp only [hz0, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
    step*
    unfold InsNWords
    intro a ha k hk
    have e2 : ∀ s1 : S, L.wr (L.wr s1 dest ⟨(encodeF c).1⟩) (core.num.U64.wrapping_add dest 8#u64) ⟨(encodeF c).2⟩ =
        wrCap (L := L) s1 dest c := fun _ => rfl
    subst_vars
    try rw [e2]
    have hz : nextOf (L.mem s) src ≠ 0#u64 := hz0
    obtain ⟨hn, hnd, hns⟩ := hnx.resolve_left hz
    have hne' := Ne.symm hne
    have hnd' := Ne.symm hnd
    have hns' := Ne.symm hns
    generalize hN : nextOf (L.mem s) src = N at *
    clear * - hP ha hs hd hn hne hne' hnd hns hnd' hns' hz hk
    simp only [wrCap_eq] <;>
      simp only [mem_wr_slot hP, ha, hs, hd, hn, hk, off0, off8, off16, off24, ne_eq, not_true_eq_false,
        false_and, ↓reduceIte] <;>
      rcases hk with rfl | rfl | rfl | rfl <;> by_cases h1 : a = dest <;> by_cases h2 : a = src <;>
      by_cases h3 : a = N <;>
      (try subst h1) <;> (try subst h2) <;> (try subst h3) <;>
      first
      | exact absurd rfl hne
      | exact absurd rfl hnd
      | exact absurd rfl hns
      | simp only [lit_ne, true_and, and_true, and_false, false_and, ↓reduceIte, and_self,
          not_false_eq_true, *]

section Fields
variable {s s' : S} {c : capability.Cap} {src dest : U64}

theorem InsNWords.capAt' (hW : InsNWords (L := L) th s s' c src dest) {a : U64} (ha : IsSlot th a)
    (he : EncWf c) :
    capAt (L.mem s') a = if a = dest then ok c else capAt (L.mem s) a := by
  rw [capAt_words, hW a ha _ off0, hW a ha _ off8]
  by_cases h1 : a = dest
  · simp [h1, decode_enc c he]
  · by_cases h2 : a = src
    · subst h2; simp [h1, lit_ne]; rw [← capAt_words]
    · simp [h1, h2, lit_ne]; rw [← capAt_words]

theorem InsNWords.prevOf' (hW : InsNWords (L := L) th s s' c src dest) {a : U64} (ha : IsSlot th a)
    (hNs : nextOf (L.mem s) src ≠ src) :
    prevOf (L.mem s') a = if a = dest then src
      else if nextOf (L.mem s) src ≠ 0#u64 ∧ a = nextOf (L.mem s) src then dest else prevOf (L.mem s) a := by
  unfold prevOf; rw [hW a ha _ off16]
  by_cases h1 : a = dest
  · simp [h1, lit_ne]
  · by_cases h2 : a = src
    · subst h2
      have : a ≠ nextOf (L.mem s) a := Ne.symm hNs
      simp [h1, lit_ne, this]
    · simp [h1, h2]

theorem InsNWords.nextOf' (hW : InsNWords (L := L) th s s' c src dest) (hP : Placed th) {a : U64} (ha : IsSlot th a)
    (hd : IsSlot th dest) (hN : Canonical (nextOf (L.mem s) src)) :
    nextOf (L.mem s') a = if a = dest then nextOf (L.mem s) src
      else if a = src then dest else nextOf (L.mem s) a := by
  rw [show nextOf (L.mem s') a = ⟨sextF (L.mem s' (wordOf a 24#u64)).bv⟩ from rfl, hW a ha _ off24]
  by_cases h1 : a = dest
  · simp only [h1, ↓reduceIte, lit_ne]
    rw [sextF_setBitF _ _ (Or.inr rfl), sextF_setBitF _ _ (Or.inl rfl), sextF_setNextF, sextF_canonical _ hN]
  · by_cases h2 : a = src
    · subst h2
      simp only [h1, ↓reduceIte]
      rw [sextF_setNextF, sextF_canonical _ (hd.canonical hP)]
    · simp only [h1, h2, ↓reduceIte, lit_ne, and_false]; rfl

theorem InsNWords.revOf' (hW : InsNWords (L := L) th s s' c src dest) {a : U64} (ha : IsSlot th a) :
    revOf (L.mem s') a = if a = dest then true else revOf (L.mem s) a := by
  rw [show revOf (L.mem s') a = (L.mem s' (wordOf a 24#u64)).bv.getLsbD 48 from rfl, hW a ha _ off24]
  by_cases h1 : a = dest
  · simp only [h1, ↓reduceIte, lit_ne]
    show (setBitF (setBitF _ 48 _) 49 _).getLsbD 48 = _
    rw [getLsbD_setBitF _ _ _ (Or.inr rfl) (Or.inl rfl), getLsbD_setBitF _ _ _ (Or.inl rfl) (Or.inl rfl)]
    simp
  · by_cases h2 : a = src
    · subst h2
      simp only [h1, ↓reduceIte]
      show (setNextF _ _).getLsbD 48 = _
      rw [getLsbD_setNextF _ _ 48 (le_refl _) (by decide)]; rfl
    · simp only [h1, h2, ↓reduceIte, lit_ne, and_false]; rfl

theorem InsNWords.fbOf' (hW : InsNWords (L := L) th s s' c src dest) {a : U64} (ha : IsSlot th a) :
    fbOf (L.mem s') a = if a = dest then true else fbOf (L.mem s) a := by
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

end Fields

end InsertNewMem

section Frame
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

attribute [local step] set_cap_spec

theorem wr_slot_other (hP : Placed th) {b : U64} (hb : IsSlot th b) {k : U64} (hk : Off k) (s : S) (v w : U64)
    (hw : P1.Aligned w) (hout : ¬ (b.val ≤ w.val ∧ w.val < b.val + 32)) :
    L.mem (L.wr s (wordOf b k) v) w = L.mem s w :=
  L.mem_wr_ne (slot_word_aligned hP hb hk) hw (by rw [slot_word_val hP hb hk]; have := hk.lt; omega)

/-- **`insert_new_cap` writes only the words of `src`, `dest` and `src`'s
old next slot.** -/
theorem insert_new_frame (hP : Placed th) (s : S) (c : capability.Cap) (src dest : U64)
    (hs : IsSlot th src) (hd : IsSlot th dest)
    (hnx : nextOf (L.mem s) src = 0#u64 ∨ IsSlot th (nextOf (L.mem s) src)) :
    cdt.insert_new_cap st s src dest c ⦃ s' => ∀ w : U64, P1.Aligned w →
      (∀ a, (a = src ∨ a = dest ∨ (nextOf (L.mem s) src ≠ 0#u64 ∧ a = nextOf (L.mem s) src)) →
        ¬ (a.val ≤ w.val ∧ w.val < a.val + 32)) → L.mem s' w = L.mem s w ⦄ := by
  unfold cdt.insert_new_cap
  step; step; step; step; step; step
  simp only [obj.Slot.is_null, bind_ok]
  subst next_post
  by_cases hz0 : nextOf (L.mem s) src = 0#u64
  · simp only [hz0, decide_true, ↓reduceIte, bind_ok]
    step*
    have hw := s'_post1
    have hout := s'_post2
    subst_vars
    have e2 : ∀ s1 : S, L.wr (L.wr s1 dest ⟨(encodeF c).1⟩) (core.num.U64.wrapping_add dest 8#u64) ⟨(encodeF c).2⟩ =
        wrCap (L := L) s1 dest c := fun _ => rfl
    rw [e2, wrCap_eq]
    have hdo := hout dest (Or.inr (Or.inl rfl))
    have hso := hout src (Or.inl rfl)
    simp only [wr_slot_other hP hd off0 _ _ w hw hdo, wr_slot_other hP hd off8 _ _ w hw hdo,
      wr_slot_other hP hd off16 _ _ w hw hdo, wr_slot_other hP hd off24 _ _ w hw hdo,
      wr_slot_other hP hs off24 _ _ w hw hso]
  · simp only [hz0, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
    step*
    have hw := s'_post1
    have hout := s'_post2
    subst_vars
    have e2 : ∀ s1 : S, L.wr (L.wr s1 dest ⟨(encodeF c).1⟩) (core.num.U64.wrapping_add dest 8#u64) ⟨(encodeF c).2⟩ =
        wrCap (L := L) s1 dest c := fun _ => rfl
    rw [e2, wrCap_eq]
    have hn := hnx.resolve_left hz0
    have hdo := hout dest (Or.inr (Or.inl rfl))
    have hso := hout src (Or.inl rfl)
    have hno := hout _ (Or.inr (Or.inr ⟨hz0, rfl⟩))
    simp only [wr_slot_other hP hd off0 _ _ w hw hdo, wr_slot_other hP hd off8 _ _ w hw hdo,
      wr_slot_other hP hd off16 _ _ w hw hdo, wr_slot_other hP hd off24 _ _ w hw hdo,
      wr_slot_other hP hs off24 _ _ w hw hso, wr_slot_other hP hn off16 _ _ w hw hno]

end Frame

/-! ## The spec's `create_cap` -/

/-- The state after `create_cap`'s CDT and original-flag updates. -/
def newCapCdt (σ : Fl4Spec.State Unit) (untyped dest : Fl4Spec.CslotPtr) : Fl4Spec.State Unit :=
  { σ with cdt := Function.update σ.cdt dest (some untyped),
           isOriginalCap := Function.update σ.isOriginalCap dest true }

theorem createCap_eq (type : Fl4Spec.ApiObjectType) (bits : Nat) (untyped dest : Fl4Spec.CslotPtr) (dev : Bool)
    (oref : Fl4Spec.ObjRef) (σ σ' : Fl4Spec.State Unit)
    (h : Fl4Spec.setCap (Z := Unit) (Fl4Spec.defaultCap type oref bits dev) dest (newCapCdt σ untyped dest) =
      ({((), σ')}, False)) :
    Fl4Spec.createCap (Z := Unit) type bits untyped dev (dest, oref) σ = ({((), σ')}, False) := by
  unfold Fl4Spec.createCap
  show (Fl4Spec.NonDet.gets _ >>= _) σ = _
  rw [nd_bind_single (gets_eq _ σ)]
  show (Fl4Spec.NonDet.gets _ >>= _) σ = _
  rw [nd_bind_single (gets_eq _ σ)]
  show (Fl4Spec.setCdt _ >>= _) σ = _
  rw [nd_bind_one (setCdt_eq _ σ)]
  show (Fl4Spec.doExtendedOp _ >>= _) _ = _
  rw [nd_bind_single (doExtendedOp_unit _ _)]
  show (Fl4Spec.setOriginal _ _ >>= _) _ = _
  rw [nd_bind_one (setOriginal_eq _ _ _)]
  exact h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`insert_new_cap` refines `create_cap`'s updates**: from related states,
with `src` a non-null CNode slot (the untyped's) and `dest` a null CNode
slot, and `c` related to `a`, FL4's `insert_new_cap src dest c` ends in a
state related to the spec's after setting `dest`'s CDT parent to `src`, its
original flag, and its cap to `a`; the ghost tree grows by `dest` as a child
of `src`. -/
theorem insert_new_refines (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    {ps pd : U64} {rs rd : Nat} (hps : th ps = some (.cnode rs)) (hpd : th pd = some (.cnode rd))
    {idxs idxd : List Bool} (hls : idxs.length = rs) (hld : idxd.length = rd)
    {srcC : capability.Cap} (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok srcC)
    (hsnn : srcC ≠ .Null)
    (hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null)
    (c : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel c a) (hcv : CapValid th c) (he : EncWf c)
    (hcnn : c ≠ .Null) :
    cdt.insert_new_cap st s (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)) c ⦃ s' =>
      ∃ σ', Fl4Spec.setCap (Z := Unit) a (pd.bv, idxd) (newCapCdt σ (ps.bv, idxs) (pd.bv, idxd)) =
          ({((), σ')}, False) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧
        MdbLinks th (L.mem s') (insG G (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)) true) ∧
        CdtRel th (L.mem s') σ' (insG G (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)) true) ∧
        InsNWords (L := L) th s s' c (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)) ⦄ := by
  have hAs : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hAd : AbsSlot th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
  set src := cslotAddr (ps.bv, idxs) with hsrcdef
  set dest := cslotAddr (pd.bv, idxd) with hdestdef
  have hs : IsSlot th src := hAs.isSlot
  have hd : IsSlot th dest := hAd.isSlot
  have hne : src ≠ dest := by
    intro e; rw [e, hdst] at hsrcC
    have : capability.Cap.Null = srcC := by simpa using hsrcC
    exact hsnn this.symm
  have hsrcm : src ∈ G.chains.flatten := (hM.members src).2 ⟨hs, srcC, hsrcC, hsnn⟩
  have hdestm : dest ∉ G.chains.flatten := by
    intro h; obtain ⟨-, c0, h0, hn⟩ := (hM.members dest).1 h
    rw [hdst] at h0
    have : capability.Cap.Null = c0 := by simpa using h0
    exact hn this.symm
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src) := by
    rcases hM.next_mem hsrcm with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, fun e => hdestm (e ▸ h1), h2⟩
  have hNs : nextOf (L.mem s) src ≠ src := by
    rcases hnx with h | ⟨-, -, h⟩
    · rw [h]; exact (hs.ne_zero hP).symm
    · exact h
  have hNc : Canonical (nextOf (L.mem s) src) := by
    rcases hnx with h | ⟨h, -, -⟩
    · rw [h]; exact canonical_zero
    · exact h.canonical hP
  apply WP.spec_mono (insert_new_mem hP s c src dest hs hd hne hnx)
  intro s' hW
  set σ1 := newCapCdt σ (ps.bv, idxs) (pd.bv, idxd)
  have hR1 : StateRel th (L.mem s) σ1 := StateRel.of_kheap hR rfl
  obtain ⟨csd1, hkd1, hwfd1, -⟩ := hR1.cnode pd rd hpd
  have hdestEq : dest = slotOf pd (blVal 0 idxd) := slotAddr_ofBl pd idxd
  have hcap' : ∀ x, IsSlot th x → capAt (L.mem s') x = if x = dest then ok c else capAt (L.mem s) x :=
    fun x hx => hW.capAt' hx he
  obtain ⟨hR2, hV2⟩ := StateRel.update_cnode_slot hR1 hV hP hpd hkd1 hwfd1 hld hca hcv
    (by rw [← hdestEq]; exact hcap')
  have h2 := setCap_cnode (Z := Unit) a hkd1 hwfd1 hld
  have hcase : Mdb.InsCase G.par src (if true then some src else G.par src) := Or.inl rfl
  have hL : InsLinks th (L.mem s) (L.mem s') src dest := by
    refine ⟨fun x hx => hW.prevOf' hx hNs, fun x hx => hW.nextOf' hP hx hd hNc, ⟨c, ?_, hcnn⟩, ⟨srcC, ?_, hsnn⟩, ?_⟩
    · rw [hcap' dest hd]; simp
    · rw [hcap' src hs, if_neg hne]; exact hsrcC
    · intro x hx hxd _
      rw [hcap' x hx, if_neg hxd]
  refine ⟨_, h2, hR2, hV2, MdbLinks.insert hP hM hsrcm hd hdestm hcase hL, ?_, hW⟩
  refine CdtRel.insert hP hC _ hAs hAd true true rfl rfl ?_
  intro x hx
  rw [hW.revOf' hx]

end

end
end Fl4Proofs.P3
