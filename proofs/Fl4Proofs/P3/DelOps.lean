/-
P3 (DESIGN.md §9), CSpace: **the steps of `rec_del` on FL4's side**, with
the relations, `DelInv` and the measures: swapping a zombie into its first
slot (`cap_swap_for_delete`).
-/
import Fl4Proofs.P3.DelInv
import Fl4Proofs.P3.MdbStepOps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## A zombie's first slot -/

theorem replicate_eq_bitsOf (k : Nat) : List.replicate k false = bitsOf 0 k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [bitsOf, List.replicate_succ, ih]

theorem home_addr (p : U64) (k : Nat) : cslotAddr (p.bv, List.replicate k false) = p := by
  show slotAddr p.bv (Fl4Spec.ofBl _) = p
  rw [slotAddr_ofBl, replicate_eq_bitsOf, blVal_bitsOf]
  simp only [Nat.zero_mul, Nat.zero_mod, Nat.add_zero]
  show (⟨p.bv + BitVec.ofNat 64 0 * 32#64⟩ : U64) = p
  simp

theorem zombieBits_tcb {zt : U64} (h : zt.val = 65) : zombieBits zt = none := by simp [zombieBits, h]
theorem zombieBits_cnode {zt : U64} (h : zt.val ≠ 65) : zombieBits zt = some zt.val := by simp [zombieBits, h]

/-- The spec's first slot of a zombie. -/
abbrev homeSl (p zt : U64) : Fl4Spec.CslotPtr := (p.bv, List.replicate (Fl4Spec.zombieCteBits (zombieBits zt)) false)

theorem home_abs {th : TypedHeap} {p zt n : U64} (h : ZOK th p zt n) : AbsSlot th (homeSl p zt) := by
  rcases h with ⟨h65, ht, -⟩ | ⟨h65, hc, -⟩
  · refine ⟨p, rfl, Or.inr ⟨ht, 0, by decide, ?_⟩⟩
    show List.replicate (Fl4Spec.zombieCteBits (zombieBits zt)) false = _
    rw [zombieBits_tcb h65]; rfl
  · refine ⟨p, rfl, Or.inl ?_⟩
    show th p = some (.cnode (List.replicate (Fl4Spec.zombieCteBits (zombieBits zt)) false).length)
    rw [zombieBits_cnode h65]; simpa [Fl4Spec.zombieCteBits] using hc

theorem firstCslot_zombie (p zt n : U64) :
    Fl4Spec.firstCslotOf (absCap (.Zombie p zt n)) = homeSl p zt := rfl

/-! ## The measure across a swap of a zombie into its first slot -/

section
variable {th : TypedHeap}

theorem nnS_ren (G : MdbGhost) (e : U64 ≃ U64) : nnS (renG G e) = (nnS G).image e := by
  unfold nnS renG
  simp only
  rw [← List.map_flatten]; ext y; simp only [List.mem_toFinset, List.mem_map, Finset.mem_image, List.mem_flatten]

theorem psi_swap {mem mem' : U64 → U64} {G : MdbGhost} {p x : U64} (hM : MdbLinks th mem G)
    (hM' : MdbLinks th mem' (renG G (Equiv.swap p x)))
    (hcap : ∀ y, IsSlot th y → capV mem' y = if y = x then capV mem p else if y = p then capV mem x else capV mem y)
    (hxs : IsSlot th x) (hpx : p ≠ x) {zt n : U64} (hz : capV mem x = .Zombie p zt n) (hnh : ¬ HomeZ mem p) :
    psiD mem' (renG G (Equiv.swap p x)) < psiD mem G ∧ (nnS (renG G (Equiv.swap p x))).card = (nnS G).card := by
  have hcard : (nnS (renG G (Equiv.swap p x))).card = (nnS G).card := by
    rw [nnS_ren]; exact Finset.card_image_of_injective _ (Equiv.injective _)
  refine ⟨?_, hcard⟩
  unfold psiD
  rw [hcard]
  have hxm : x ∈ mzS mem G := by
    rw [mem_mzS hM]
    refine ⟨hxs, by rw [hz]; simp, ?_⟩
    rintro ⟨zt', n', h⟩; rw [hz] at h; cases h; exact hpx rfl
  have hsub : mzS mem' (renG G (Equiv.swap p x)) ⊆ ((mzS mem G).erase x).image (Equiv.swap p x) := by
    intro z hz'
    have hz1 : z ∈ nnS (renG G (Equiv.swap p x)) := (Finset.mem_filter.1 hz').1
    have hz2 : ¬ HomeZ mem' z := (Finset.mem_filter.1 hz').2
    rw [nnS_ren, Finset.mem_image] at hz1
    obtain ⟨y, hy, rfl⟩ := hz1
    have hys : IsSlot th y := ((mem_nnS hM y).1 hy).1
    refine Finset.mem_image.2 ⟨y, Finset.mem_erase.2 ⟨?_, ?_⟩, rfl⟩
    · rintro rfl
      apply hz2
      rw [Equiv.swap_apply_right]
      refine ⟨zt, n, ?_⟩
      rw [hcap p ((mem_nnS hM' _).1 (by rw [nnS_ren]; exact Finset.mem_image.2 ⟨y, hy, by rw [Equiv.swap_apply_right]⟩)).1,
        if_neg hpx, if_pos rfl, hz]
    · rw [mem_mzS hM]
      refine ⟨hys, ((mem_nnS hM y).1 hy).2, ?_⟩
      by_cases hyp : y = p
      · subst hyp; exact hnh
      · by_cases hyx : y = x
        · subst hyx; rintro ⟨zt', n', h⟩; rw [hz] at h; cases h; exact hpx rfl
        · rw [Equiv.swap_apply_of_ne_of_ne hyp hyx] at hz2
          intro hh; apply hz2
          obtain ⟨zt', n', h⟩ := hh
          exact ⟨zt', n', by rw [hcap y hys, if_neg hyx, if_neg hyp, h]⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := (mzS mem G).erase x) (f := Equiv.swap p x)
  have h3 := Finset.card_erase_of_mem hxm
  have h4 : 0 < (mzS mem G).card := Finset.card_pos.2 ⟨x, hxm⟩
  omega

end

/-! ## `cap_swap_for_delete` of a zombie into its first slot -/

theorem slot_eq_eq' (a b : obj.Slot) : obj.Slot.Insts.CoreCmpPartialEqSlot.eq a b = ok (decide (a = b)) := rfl

theorem capSwapForDelete_eq {σ σ' : Fl4Spec.State Unit} {sl1 sl2 : Fl4Spec.CslotPtr} {a1 a2 : Fl4Spec.Cap}
    (hne : sl1 ≠ sl2) (h1 : Fl4Spec.getCap (Z := Unit) sl1 σ = ({(a1, σ)}, False))
    (h2 : Fl4Spec.getCap (Z := Unit) sl2 σ = ({(a2, σ)}, False))
    (hs : Fl4Spec.capSwap (Z := Unit) a1 sl1 a2 sl2 σ = ({((), σ')}, False)) :
    Fl4Spec.capSwapForDelete (Z := Unit) sl1 sl2 σ = ({((), σ')}, False) := by
  unfold Fl4Spec.capSwapForDelete Fl4Spec.NonDet.when
  rw [if_pos hne]
  show (Fl4Spec.getCap sl1 >>= _) σ = _
  rw [nd_bind_one h1]
  show (Fl4Spec.getCap sl2 >>= _) σ = _
  rw [nd_bind_one h2]
  exact hs

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **Swapping the zombie at `x` into its first slot `p`**: the spec's
`cap_swap_for_delete`, the relations and `DelInv` kept, the measure smaller,
the other slots changed as `ChgOK` allows. -/
theorem swap_home (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hD : DelInv th (L.mem s)) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl) {p zt n : U64}
    (hx : capAt (L.mem s) (cslotAddr sl) = ok (.Zombie p zt n)) (hpx : p ≠ cslotAddr sl) :
    cdt.cap_swap_for_delete st s p (cslotAddr sl) ⦃ s' => ∃ σ' G',
      Fl4Spec.capSwapForDelete (Z := Unit) (homeSl p zt) sl σ = ({((), σ')}, False) ∧
      CRel th (L.mem s') σ' G' ∧ DelInv th (L.mem s') ∧ psiD (L.mem s') G' < psiD (L.mem s) G ∧
      (nnS G').card = (nnS G).card ∧
      (∀ y, IsSlot th y → y ≠ cslotAddr sl → ChgOK (L.mem s) (L.mem s') y) ∧
      capV (L.mem s') p = .Zombie p zt n ∧ capV (L.mem s') (cslotAddr sl) = capV (L.mem s) p ∧
      G' = renG G (Equiv.swap p (cslotAddr sl)) ∧
      (∀ y, IsSlot th y → capV (L.mem s') y = if y = cslotAddr sl then capV (L.mem s) p
        else if y = p then capV (L.mem s) (cslotAddr sl) else capV (L.mem s) y) ∧
      MdbStep (L.mem s) G (L.mem s') G' ⦄ := by
  set x := cslotAddr sl with hxdef
  have hxs : IsSlot th x := hA.isSlot
  have hzok := hD.zwf x hxs p zt n (capV_of_capAt hx)
  have hH := home_abs hzok
  have hHa : cslotAddr (homeSl p zt) = p := home_addr p _
  have hps : IsSlot th p := by rw [← hHa]; exact hH.isSlot
  have hne : homeSl p zt ≠ sl := fun e => hpx (by rw [← hHa, e])
  have hnh : ¬ HomeZ (L.mem s) p := by
    rintro ⟨zt', n', h⟩
    exact hD.zu p x hps hxs hpx p zt' n' p zt n h (capV_of_capAt hx) rfl
  have hxm : x ∈ G.chains.flatten := (hM.members _).2 ⟨hxs, _, hx, by simp⟩
  have hZn : capability.Cap.Zombie p zt n ≠ .Null := by simp
  unfold cdt.cap_swap_for_delete
  rw [slot_eq_eq', decide_eq_false hpx]
  simp only [Bool.false_eq_true, ↓reduceIte, slot_cap_eq, capAt_capV, bind_ok]
  rw [capV_of_capAt hx]
  obtain ⟨c1, a1, hc1, hca1, hg1⟩ := hR.abs_cap hH
  rw [hHa] at hc1
  rw [hca1.abs] at hg1
  rw [capV_of_capAt hc1]
  obtain ⟨c2, a2, hc2, hca2, hg2⟩ := hR.abs_cap hA
  rw [hx] at hc2; cases eq_of_ok_eq hc2
  have hcv : ∀ y, IsSlot th y → ∀ c, capAt (L.mem s) y = ok c → capV (L.mem s) y = c := fun _ _ _ h => capV_of_capAt h
  have hcvx : capV (L.mem s) x = .Zombie p zt n := capV_of_capAt hx
  have post : ∀ (s' : S) (σ' : Fl4Spec.State Unit), StateRel th (L.mem s') σ' → SlotsValid th (L.mem s') →
      MdbLinks th (L.mem s') (renG G (Equiv.swap p x)) → CdtRel th (L.mem s') σ' (renG G (Equiv.swap p x)) →
      MdbInv (L.mem s') (renG G (Equiv.swap p x)) →
      (∀ y, IsSlot th y → capV (L.mem s') y =
        if y = x then capV (L.mem s) p else if y = p then capV (L.mem s) x else capV (L.mem s) y) →
      (∀ y, IsSlot th y → capV (L.mem s') y = .Null → prevOf (L.mem s') y = 0#u64 ∧ nextOf (L.mem s') y = 0#u64) →
      MdbStep (L.mem s) G (L.mem s') (renG G (Equiv.swap p x)) →
      Fl4Spec.capSwapForDelete (Z := Unit) (homeSl p zt) sl σ = ({((), σ')}, False) →
      ∃ σ' G', Fl4Spec.capSwapForDelete (Z := Unit) (homeSl p zt) sl σ = ({((), σ')}, False) ∧
        CRel th (L.mem s') σ' G' ∧ DelInv th (L.mem s') ∧ psiD (L.mem s') G' < psiD (L.mem s) G ∧
        (nnS G').card = (nnS G).card ∧
        (∀ y, IsSlot th y → y ≠ x → ChgOK (L.mem s) (L.mem s') y) ∧
        capV (L.mem s') p = .Zombie p zt n ∧ capV (L.mem s') x = capV (L.mem s) p ∧
        G' = renG G (Equiv.swap p x) ∧
        (∀ y, IsSlot th y → capV (L.mem s') y = if y = x then capV (L.mem s) p
          else if y = p then capV (L.mem s) x else capV (L.mem s) y) ∧
        MdbStep (L.mem s) G (L.mem s') G' := by
    intro s' σ' hR' hV' hM' hC' hI' hcap hnc hstep hsw
    obtain ⟨hlt, hcd⟩ := psi_swap hM hM' hcap hxs hpx hcvx hnh
    refine ⟨σ', _, hsw, ⟨hR', hV', hM', hC', hI'⟩, ⟨?_, ?_, hnc⟩, hlt, hcd, ?_, ?_, ?_, rfl, hcap, hstep⟩
    · intro y hy p' zt' n' hy'
      rw [hcap y hy] at hy'
      split_ifs at hy' with h1 h2
      · exact hD.zwf p hps _ _ _ hy'
      · exact hD.zwf x hxs _ _ _ hy'
      · exact hD.zwf y hy _ _ _ hy'
    · intro y y' hy hy' hyy p1 zt1 n1 p2 zt2 n2 h1 h2
      rw [hcap y hy] at h1
      rw [hcap y' hy'] at h2
      let e := Equiv.swap p x
      have he : ∀ w, IsSlot th w → capV (L.mem s') w = capV (L.mem s) (e w) := by
        intro w hw
        rw [hcap w hw]
        by_cases hw1 : w = x
        · rw [if_pos hw1, hw1, Equiv.swap_apply_right]
        · by_cases hw2 : w = p
          · rw [if_neg hw1, if_pos hw2, hw2, Equiv.swap_apply_left]
          · rw [if_neg hw1, if_neg hw2, Equiv.swap_apply_of_ne_of_ne hw2 hw1]
      have hes : ∀ w, IsSlot th w → IsSlot th (e w) := by
        intro w hw
        by_cases hw1 : w = x
        · rw [hw1, Equiv.swap_apply_right]; exact hps
        · by_cases hw2 : w = p
          · rw [hw2, Equiv.swap_apply_left]; exact hxs
          · rw [Equiv.swap_apply_of_ne_of_ne hw2 hw1]; exact hw
      rw [← hcap y hy, he y hy] at h1
      rw [← hcap y' hy', he y' hy'] at h2
      exact hD.zu _ _ (hes y hy) (hes y' hy') (fun h => hyy (e.injective h)) _ _ _ _ _ _ h1 h2
    · intro y hy hyx
      rw [ChgOK, hcap y hy, if_neg hyx]
      by_cases hyp : y = p
      · rw [if_pos hyp, hyp]
        exact Or.inr ⟨Or.inr ⟨zt, n, by rw [hcap p hps, if_neg hpx, if_pos rfl, hcvx]⟩, hnh⟩
      · rw [if_neg hyp]; exact Or.inl rfl
    · rw [hcap p hps, if_neg hpx, if_pos rfl, hcvx]
    · rw [hcap x hxs, if_pos rfl]
  by_cases hc1n : c1 = .Null
  · subst hc1n
    obtain ⟨hp0, hn0⟩ := hD.nc p hps (capV_of_capAt hc1)
    have hsn := swap_null_full th s σ G hR hV hP hM hC hI hH hA hne (by rw [hHa]; exact hc1)
      (by rw [hHa]; exact hp0) (by rw [hHa]; exact hn0) hx hZn
    rw [hHa] at hsn
    refine WP.spec_mono hsn ?_
    rintro s' ⟨σ', G', hsw, hR', hV', hM', hC', hI', hG', hxp0, hxn0, hnl, hcp, hstep⟩
    subst hG'
    have hcap : ∀ y, IsSlot th y → capV (L.mem s') y =
        if y = x then capV (L.mem s) p else if y = p then capV (L.mem s) x else capV (L.mem s) y := by
      intro y hy
      have := hcp y hy
      rw [capV_of_capAt hc1, hcvx]
      split_ifs at this ⊢ with h1 h2
      · exact capV_of_capAt this
      · exact capV_of_capAt this
      · exact capV_of_capAt (this.trans (capAt_capV _ _))
    have hnc : ∀ y, IsSlot th y → capV (L.mem s') y = .Null → prevOf (L.mem s') y = 0#u64 ∧ nextOf (L.mem s') y = 0#u64 := by
      intro y hy hy0
      by_cases h1 : y = x
      · subst h1; exact ⟨hxp0, hxn0⟩
      by_cases h2 : y = p
      · subst h2; rw [hcap y hy, if_neg h1, if_pos rfl, hcvx] at hy0; cases hy0
      rw [hcap y hy, if_neg h1, if_neg h2] at hy0
      obtain ⟨e1, e2⟩ := hnl y hy h2 h1 (by rw [capAt_capV, capAt_capV, hcap y hy, if_neg h1, if_neg h2])
        (by rw [capAt_capV, hy0])
      rw [e1, e2]; exact hD.nc y hy hy0
    have := post s' σ' hR' hV' hM' hC' hI' hcap hnc hstep
      (capSwapForDelete_eq hne hg1 (by rw [hca2.abs] at hg2; exact hg2) hsw)
    rw [capV_of_capAt hc1, hcvx] at this; exact this
  · have he1 : EncWf c1 := by rw [capAt_words] at hc1; exact decode_encWf hc1
    have he2 : EncWf (capability.Cap.Zombie p zt n) := by rw [capAt_words] at hx; exact decode_encWf hx
    have hsf := swap_full_abs th s σ G hR hV hP hM hC hI hH hA hne (by rw [hHa]; exact hc1) hc1n hx hZn
      c1 a1 hca1 (hV.abs hH (by rw [hHa]; exact hc1)) he1 hc1n rfl rfl
      (.Zombie p zt n) a2 hca2 (hV.abs hA hx) he2 hZn rfl rfl
    rw [hHa] at hsf
    have hpm : p ∈ G.chains.flatten := (hM.members _).2 ⟨hps, c1, hc1, hc1n⟩
    have hms := swap_mstep hP s G hM hpm hxm hpx c1 (.Zombie p zt n) he1 he2 (by rw [capV_of_capAt hc1])
      (by rw [capV_of_capAt hc1]) (by rw [hcvx]) (by rw [hcvx])
      (by rw [capV_of_capAt hc1]; exact fun _ _ _ _ _ h => h) (by rw [hcvx]; exact fun _ _ _ _ _ h => h)
    refine WP.spec_mono (WP.spec_and hsf hms) ?_
    rintro s' ⟨⟨σ', G', hsw, hR', hV', hM', hC', hI', hG', hcp, hnl⟩, hst⟩
    have hstep := hst (fun _ => by rw [capV_of_capAt hc1]) (fun _ => by rw [hcvx])
    subst hG'
    have hcap : ∀ y, IsSlot th y → capV (L.mem s') y =
        if y = x then capV (L.mem s) p else if y = p then capV (L.mem s) x else capV (L.mem s) y := by
      intro y hy
      have := hcp y hy
      rw [capV_of_capAt hc1, hcvx]
      split_ifs at this ⊢ with h1 h2
      · exact capV_of_capAt this
      · exact capV_of_capAt this
      · exact capV_of_capAt (this.trans (capAt_capV _ _))
    have hnc : ∀ y, IsSlot th y → capV (L.mem s') y = .Null → prevOf (L.mem s') y = 0#u64 ∧ nextOf (L.mem s') y = 0#u64 := by
      intro y hy hy0
      by_cases h1 : y = x
      · rw [hcap y hy, if_pos h1, capV_of_capAt hc1] at hy0; exact absurd hy0 hc1n
      by_cases h2 : y = p
      · rw [hcap y hy, if_neg h1, if_pos h2, hcvx] at hy0; cases hy0
      rw [hcap y hy, if_neg h1, if_neg h2] at hy0
      have hym : y ∉ G.chains.flatten := fun h => (((mem_nnS hM y).1 (List.mem_toFinset.2 h)).2) hy0
      obtain ⟨e1, e2⟩ := hnl y hy hym h2 h1
      rw [e1, e2]; exact hD.nc y hy hy0
    have := post s' σ' hR' hV' hM' hC' hI' hcap hnc hstep (capSwapForDelete_eq hne hg1 (by rw [hca2.abs] at hg2; exact hg2)
      (by rw [hca2.abs, hca1.abs] at hsw; exact hsw))
    rw [capV_of_capAt hc1, hcvx] at this; exact this

end

/-! ## Writing a zombie into a linked slot -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem MdbLinks.recap {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    (hl : ∀ y, IsSlot th y → prevOf mem' y = prevOf mem y ∧ nextOf mem' y = nextOf mem y)
    (hnn : ∀ y, IsSlot th y → (capV mem' y = .Null ↔ capV mem y = .Null)) : MdbLinks th mem' G := by
  have hs : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x hx => ((hM.members x).1 hx).1
  refine ⟨hM.tree, hM.ne_nil, ?_, ?_, ?_, ?_⟩
  · intro ch hch
    apply (hM.chain ch hch).imp_of_mem_imp
    rintro a b ha hb ⟨h1, h2⟩
    have haf := hs a (List.mem_flatten.2 ⟨_, hch, ha⟩)
    have hbf := hs b (List.mem_flatten.2 ⟨_, hch, hb⟩)
    exact ⟨by rw [(hl a haf).2, h1], by rw [(hl b hbf).1, h2]⟩
  · intro ch hch hne
    rw [(hl _ (hs _ (List.mem_flatten.2 ⟨_, hch, List.head_mem hne⟩))).1, hM.head ch hch hne]
  · intro ch hch hne
    rw [(hl _ (hs _ (List.mem_flatten.2 ⟨_, hch, List.getLast_mem hne⟩))).2, hM.last ch hch hne]
  · intro a
    rw [hM.members a]
    constructor
    · rintro ⟨ha, c, hc, hn⟩
      refine ⟨ha, _, capAt_capV _ _, fun h => hn ?_⟩
      rw [← capV_of_capAt hc]; exact (hnn a ha).1 h
    · rintro ⟨ha, c, hc, hn⟩
      refine ⟨ha, _, capAt_capV _ _, fun h => hn ?_⟩
      rw [← capV_of_capAt hc]; exact (hnn a ha).2 h

/-- **Writing a zombie `Z` into the linked slot `x`**, in place of its cap:
`set_cap`, the relations, `MdbInv` (from the same-region facts of the old
cap), `DelInv` (from `Z` being well formed and covering no other zombie's
object), the same ghost tree, and the measure not larger. -/
theorem set_zombie (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hD : DelInv th (L.mem s)) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl)
    (hxn : capV (L.mem s) (cslotAddr sl) ≠ .Null) {p zt n : U64}
    (hZw : CapWf (.Zombie p zt n)) (hZe : EncWf (.Zombie p zt n)) (hZok : ZOK th p zt n)
    (hZu : ∀ y, IsSlot th y → y ≠ cslotAddr sl → ∀ p' zt' n', capV (L.mem s) y = .Zombie p' zt' n' → p' ≠ p)
    (hbx : isBadged (capV (L.mem s) (cslotAddr sl)) = false) (hbf : badgeF (capV (L.mem s) (cslotAddr sl)) = 0#u64)
    (h1 : ∀ y ∈ G.chains.flatten, y ≠ cslotAddr sl →
      srB (capV (L.mem s) y) (.Zombie p zt n) = srB (capV (L.mem s) y) (capV (L.mem s) (cslotAddr sl)))
    (h2 : ∀ y ∈ G.chains.flatten, y ≠ cslotAddr sl → srB (capV (L.mem s) (cslotAddr sl)) (capV (L.mem s) y) = false)
    (hhome : HomeZ (L.mem s) (cslotAddr sl) → p = cslotAddr sl) :
    obj.Slot.set_cap st (cslotAddr sl) s (.Zombie p zt n) ⦃ s' => ∃ σ',
      Fl4Spec.setCap (Z := Unit) (absCap (.Zombie p zt n)) sl σ = ({((), σ')}, False) ∧
      CRel th (L.mem s') σ' G ∧ DelInv th (L.mem s') ∧ psiD (L.mem s') G ≤ psiD (L.mem s) G ∧
      capV (L.mem s') (cslotAddr sl) = .Zombie p zt n ∧
      (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem s') y = capV (L.mem s) y) ∧
      (∀ y, IsSlot th y → revOf (L.mem s') y = revOf (L.mem s) y) ⦄ := by
  set x := cslotAddr sl with hxdef
  have hxs : IsSlot th x := hA.isSlot
  have hxm : x ∈ G.chains.flatten := (hM.members _).2 ⟨hxs, _, capAt_capV _ _, hxn⟩
  rw [set_cap_eq, WP.spec_ok]
  have hcapA : ∀ y, IsSlot th y → capAt (L.mem (wrCap (L := L) s x (.Zombie p zt n))) y =
      if y = x then ok (.Zombie p zt n) else capAt (L.mem s) y := fun y hy => capAt_wrCap hP s hxs hZe hy
  have hcap : ∀ y, IsSlot th y → capV (L.mem (wrCap (L := L) s x (.Zombie p zt n))) y =
      if y = x then .Zombie p zt n else capV (L.mem s) y := by
    intro y hy
    have := hcapA y hy
    split_ifs at this ⊢
    · exact capV_of_capAt this
    · exact capV_of_capAt (this.trans (capAt_capV _ _))
  have hl : ∀ y, IsSlot th y → prevOf (L.mem (wrCap (L := L) s x (.Zombie p zt n))) y = prevOf (L.mem s) y ∧
      nextOf (L.mem (wrCap (L := L) s x (.Zombie p zt n))) y = nextOf (L.mem s) y ∧
      revOf (L.mem (wrCap (L := L) s x (.Zombie p zt n))) y = revOf (L.mem s) y ∧
      fbOf (L.mem (wrCap (L := L) s x (.Zombie p zt n))) y = fbOf (L.mem s) y := fun y hy =>
    ⟨prevOf_wrCap hP hy hxs s _, nextOf_wrCap hP hy hxs s _, revOf_wrCap hP hy hxs s _, fbOf_wrCap hP hy hxs s _⟩
  obtain ⟨σ', hσ', hR', hV', hσe, -⟩ := StateRel.update_abs_slot hR hV hP hA (show CapRel (.Zombie p zt n) _ from ⟨hZw, rfl⟩)
    trivial hcapA
  have hother : ∀ y, IsSlot th y → y ≠ x → capV (L.mem (wrCap (L := L) s x (.Zombie p zt n))) y = capV (L.mem s) y :=
    fun y hy hyx => by rw [hcap y hy, if_neg hyx]
  have hZx : capV (L.mem (wrCap (L := L) s x (.Zombie p zt n))) x = .Zombie p zt n := by rw [hcap x hxs, if_pos rfl]
  have hM' : MdbLinks th (L.mem (wrCap (L := L) s x (.Zombie p zt n))) G :=
    hM.recap (fun y hy => ⟨(hl y hy).1, (hl y hy).2.1⟩) (fun y hy => by
      by_cases hyx : y = x
      · rw [hyx, hZx]; simp [hxn]
      · rw [hother y hy hyx])
  have hC' : CdtRel th (L.mem (wrCap (L := L) s x (.Zombie p zt n))) σ' G := by
    refine ⟨fun sl' hs' => ?_, fun sl' q hq => ?_, fun sl' hs' => ?_, hC.par_slot⟩
    · rw [hσe]; exact hC.cdt sl' hs'
    · rw [hσe] at hq; exact hC.cdt_slot sl' q hq
    · rw [hσe]; show σ.isOriginalCap sl' = _; rw [hC.orig sl' hs', (hl _ hs'.isSlot).2.2.1]
  have hI' : MdbInv (L.mem (wrCap (L := L) s x (.Zombie p zt n))) G :=
    MdbInv.zombify hM hI hxm hl (fun y hy hyx => hother y hy hyx) hZx hbx hbf h1 h2
  refine ⟨σ', hσ', ⟨hR', hV', hM', hC', hI'⟩, ⟨?_, ?_, ?_⟩, ?_, hZx, hother, fun y hy => (hl y hy).2.2.1⟩
  · intro y hy p' zt' n' h
    by_cases hyx : y = x
    · rw [hyx, hZx] at h; cases h; exact hZok
    · rw [hother y hy hyx] at h; exact hD.zwf y hy _ _ _ h
  · intro y y' hy hy' hyy p1 zt1 n1 p2 zt2 n2 e1 e2
    by_cases hyx : y = x
    · rw [hyx, hZx] at e1; cases e1
      have hy'x : y' ≠ x := fun e => hyy (hyx.trans e.symm)
      rw [hother y' hy' hy'x] at e2
      exact (hZu y' hy' hy'x _ _ _ e2).symm
    · by_cases hy'x : y' = x
      · rw [hy'x, hZx] at e2; cases e2
        rw [hother y hy hyx] at e1
        exact hZu y hy hyx _ _ _ e1
      · rw [hother y hy hyx] at e1; rw [hother y' hy' hy'x] at e2
        exact hD.zu y y' hy hy' hyy _ _ _ _ _ _ e1 e2
  · intro y hy h0
    by_cases hyx : y = x
    · rw [hyx, hZx] at h0; cases h0
    · rw [hother y hy hyx] at h0; rw [(hl y hy).1, (hl y hy).2.1]; exact hD.nc y hy h0
  · refine psiD_le hM hM' (fun y hy h => ?_) (fun y hy _ hh => ?_)
    · by_cases hyx : y = x
      · rw [hyx]; exact hxn
      · rw [← hother y hy hyx]; exact h
    · by_cases hyx : y = x
      · intro hx'; apply hh; rw [hyx] at hx' ⊢
        have := hhome hx'; exact ⟨zt, n, by rw [hZx, this]⟩
      · intro hx'; apply hh; obtain ⟨zt', n', e⟩ := hx'; exact ⟨zt', n', by rw [hother y hy hyx, e]⟩

end

end

end Fl4Proofs.P3
