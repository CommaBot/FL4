/-
P3 (DESIGN.md §9), untyped: the CNode operations refine the spec and keep
both `MdbInv` and **`UtInv`** (`insert_full_ut`, `move_full_ut`,
`swap_full_ut`, `empty_full_ut`, `delete_full_ut`), so that the untyped
invariant can be part of the state invariant.
-/
import Fl4Proofs.P3.UntypedUtOps
import Fl4Proofs.P3.Delete
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`cdt::insert` of a derived cap refines `cap_insert` and keeps `MdbInv` and `UtInv`.** -/
theorem insert_full_ut (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G) (hU : UtInv (L.mem s) G)
    {ps pd : U64} {rs rd : Nat} (hps : th ps = some (.cnode rs)) (hpd : th pd = some (.cnode rd))
    {idxs idxd : List Bool} (hls : idxs.length = rs) (hld : idxd.length = rd)
    {srcC : capability.Cap} (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok srcC)
    (hsnn : srcC ≠ .Null)
    (hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null)
    (c : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel c a) (hcv : CapValid th c) (he : EncWf c)
    (hcnn : c ≠ .Null) (hsh : shape c = shape srcC) (hbd : badgeF c = badgeF srcC ∨ badgeF srcC = 0#u64)
    (hut : isUt srcC = true → ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (ps.bv, idxs))) (hzb : isZb srcC = false)
    (hutc : isUt srcC = true → c = srcC) :
    cdt.insert st s c (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)) ⦃ s' =>
      ∃ σ' G', Fl4Spec.capInsert (Z := Unit) a (ps.bv, idxs) (pd.bv, idxd) σ = ({((), σ')}, False) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧ MdbLinks th (L.mem s') G' ∧
        CdtRel th (L.mem s') σ' G' ∧ MdbInv (L.mem s') G' ∧ UtInv (L.mem s') G' ⦄ := by
  have hAs : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hAd : AbsSlot th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
  have hsrcm := (hM.members _).2 ⟨hAs.isSlot, srcC, hsrcC, hsnn⟩
  have hdestm : cslotAddr (pd.bv, idxd) ∉ G.chains.flatten := by
    intro h; obtain ⟨-, c0, h0, hn⟩ := (hM.members _).1 h
    rw [hdst] at h0
    exact hn (eq_of_ok_eq h0).symm
  have hcv0 := capV_of_capAt hsrcC
  have hes : EncWf srcC := by rw [capAt_words] at hsrcC; exact decode_encWf hsrcC
  have hself : srB srcC srcC = true := by
    have := hI.self _ hsrcm (by rw [hcv0]; exact hzb); unfold srM at this; rw [hcv0] at this; exact this
  have hk := sameBadgeKind_of_shape hsh
  obtain ⟨hwf, rfl⟩ := hca
  have hb : decide (Fl4Spec.shouldBeParentOf (absCap srcC) (σ.isOriginalCap (ps.bv, idxs)) (absCap c)
      (decide (Fl4Spec.isCapRevocable (absCap c) (absCap srcC)))) =
      isPF (revOf (L.mem s) (cslotAddr (ps.bv, idxs))) srcC c (revF c srcC) := by
    rw [hC.orig _ hAs]; exact sbp_eq srcC c _ hsh hself hes hk
  have hsib : ¬ Fl4Spec.shouldBeParentOf (absCap srcC) (σ.isOriginalCap (ps.bv, idxs)) (absCap c)
      (decide (Fl4Spec.isCapRevocable (absCap c) (absCap srcC))) →
      ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (ps.bv, idxs)) := by
    intro hn
    have h0 : isPF (revOf (L.mem s) (cslotAddr (ps.bv, idxs))) srcC c (revF c srcC) = false := by
      rw [← hb]; simpa using hn
    rw [← hcv0] at h0 hsh hbd hzb
    exact MdbInv.sib (th := th) hI hsrcm hzb hsh hbd h0
  obtain ⟨s1, h1, hpost⟩ := spec_exists
    (insert_refines' th s σ G hR hV hP hM hC hps hpd hls hld hsrcC hsnn hdst c _ ⟨hwf, rfl⟩ hcv he hcnn hk)
  obtain ⟨s2, h2, hinv⟩ := spec_exists
    (insert_mdbinv hP s G hM hI hsrcm hAd.isSlot hdestm hsrcC c he hsh hbd hut hzb)
  obtain ⟨s3, h3, hut'⟩ := spec_exists
    (insert_utinv hP s G hM hI hU hsrcm hAd.isSlot hdestm hsrcC c he hsh hbd hut hzb hutc
      (isPF (revOf (L.mem s) (cslotAddr (ps.bv, idxs))) srcC c (revF c srcC)))
  rw [h1] at h2 h3
  have e := eq_of_ok_eq h2
  have e3 := eq_of_ok_eq h3
  subst e e3
  rw [h1, WP.spec_ok]
  obtain ⟨σ', G', hins, hR', hV', hM', hC', hG'⟩ := hpost hsib
  refine ⟨σ', G', hins, hR', hV', hM', hC', ?_, ?_⟩
  · rw [hG', hb]; exact hinv
  · rw [hG', hb]; exact hut'

/-- **`cdt::move_cap` refines `cap_move` and keeps `MdbInv` and `UtInv`**, for a new cap
of the old one's shape and badge. -/
theorem move_full_ut (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G) (hU : UtInv (L.mem s) G)
    {ps pd : U64} {rs rd : Nat} (hps : th ps = some (.cnode rs)) (hpd : th pd = some (.cnode rd))
    {idxs idxd : List Bool} (hls : idxs.length = rs) (hld : idxd.length = rd)
    {srcC : capability.Cap} (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok srcC)
    (hsnn : srcC ≠ .Null)
    (hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null)
    (c : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel c a) (hcv : CapValid th c) (he : EncWf c)
    (hcnn : c ≠ .Null) (hsh : shape c = shape srcC) (hbd : badgeF c = badgeF srcC)
    (hutc : isUt srcC = true → c = srcC) :
    cdt.move_cap st s c (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)) ⦃ s' =>
      ∃ σ' G', Fl4Spec.capMove (Z := Unit) a (ps.bv, idxs) (pd.bv, idxd) σ = ({((), σ')}, False) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧ MdbLinks th (L.mem s') G' ∧
        CdtRel th (L.mem s') σ' G' ∧ MdbInv (L.mem s') G' ∧ UtInv (L.mem s') G' ⦄ := by
  have hAs : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hAd : AbsSlot th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
  have hsrcm := (hM.members _).2 ⟨hAs.isSlot, srcC, hsrcC, hsnn⟩
  have hdestm : cslotAddr (pd.bv, idxd) ∉ G.chains.flatten := by
    intro h; obtain ⟨-, c0, h0, hn⟩ := (hM.members _).1 h
    rw [hdst] at h0
    exact hn (eq_of_ok_eq h0).symm
  obtain ⟨s1, h1, hpost⟩ := spec_exists
    (move_refines th s σ G hR hV hP hM hC hps hpd hls hld hsrcC hsnn hdst c a hca hcv he hcnn)
  obtain ⟨s2, h2, hinv⟩ := spec_exists
    (move_mdbinv hP s G hM hI hsrcm hAd.isSlot hdestm hsrcC c he hcnn hsh hbd)
  obtain ⟨s3, h3, hut'⟩ := spec_exists
    (move_utinv hP s G hM hU hsrcm hAd.isSlot hdestm hsrcC c he hsh hutc)
  rw [h1] at h2 h3
  have e := eq_of_ok_eq h2
  have e3 := eq_of_ok_eq h3
  subst e e3
  rw [h1, WP.spec_ok]
  obtain ⟨σ', G', hmv, hR', hV', hM', hC', hG'⟩ := hpost
  exact ⟨σ', G', hmv, hR', hV', hM', hC', by rw [hG']; exact hinv, by rw [hG']; exact hut'⟩

/-- **`cdt::swap` refines `cap_swap` and keeps `MdbInv` and `UtInv`**, for new caps of
the old ones' shapes and badges. -/
theorem swap_full_ut (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G) (hU : UtInv (L.mem s) G)
    {p1 p2 : U64} {r1 r2 : Nat} (hp1 : th p1 = some (.cnode r1)) (hp2 : th p2 = some (.cnode r2))
    {i1 i2 : List Bool} (hl1 : i1.length = r1) (hl2 : i2.length = r2)
    (hne : (p1.bv, i1) ≠ (p2.bv, i2))
    {o1 o2 : capability.Cap} (ho1 : capAt (L.mem s) (cslotAddr (p1.bv, i1)) = ok o1) (hon1 : o1 ≠ .Null)
    (ho2 : capAt (L.mem s) (cslotAddr (p2.bv, i2)) = ok o2) (hon2 : o2 ≠ .Null)
    (c1 : capability.Cap) (a1 : Fl4Spec.Cap) (hca1 : CapRel c1 a1) (hcv1 : CapValid th c1) (he1 : EncWf c1)
    (hcn1 : c1 ≠ .Null) (hsh1 : shape c1 = shape o1) (hbd1 : badgeF c1 = badgeF o1)
    (hut1 : isUt o1 = true → c1 = o1)
    (c2 : capability.Cap) (a2 : Fl4Spec.Cap) (hca2 : CapRel c2 a2) (hcv2 : CapValid th c2) (he2 : EncWf c2)
    (hcn2 : c2 ≠ .Null) (hsh2 : shape c2 = shape o2) (hbd2 : badgeF c2 = badgeF o2)
    (hut2 : isUt o2 = true → c2 = o2) :
    cdt.swap st s c1 (cslotAddr (p1.bv, i1)) c2 (cslotAddr (p2.bv, i2)) ⦃ s' =>
      ∃ σ' G', Fl4Spec.capSwap (Z := Unit) a1 (p1.bv, i1) a2 (p2.bv, i2) σ = ({((), σ')}, False) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧ MdbLinks th (L.mem s') G' ∧
        CdtRel th (L.mem s') σ' G' ∧ MdbInv (L.mem s') G' ∧ UtInv (L.mem s') G' ⦄ := by
  have hA1 : AbsSlot th (p1.bv, i1) := ⟨p1, rfl, Or.inl (by simpa [hl1] using hp1)⟩
  have hA2 : AbsSlot th (p2.bv, i2) := ⟨p2, rfl, Or.inl (by simpa [hl2] using hp2)⟩
  have hAne : cslotAddr (p1.bv, i1) ≠ cslotAddr (p2.bv, i2) := fun h => hne (cslotAddr_inj hP hA1 hA2 h)
  have hm1 := (hM.members _).2 ⟨hA1.isSlot, o1, ho1, hon1⟩
  have hm2 := (hM.members _).2 ⟨hA2.isSlot, o2, ho2, hon2⟩
  obtain ⟨s1, h1, hpost⟩ := spec_exists
    (swap_refines th s σ G hR hV hP hM hC hp1 hp2 hl1 hl2 hne ho1 hon1 ho2 hon2 c1 a1 hca1 hcv1 he1 hcn1
      c2 a2 hca2 hcv2 he2 hcn2)
  rw [← capV_of_capAt ho1] at hsh1 hbd1 hut1
  rw [← capV_of_capAt ho2] at hsh2 hbd2 hut2
  obtain ⟨s2, h2, hinv⟩ := spec_exists
    (swap_mdbinv hP s G hM hI hm1 hm2 hAne c1 c2 he1 he2 hcn1 hcn2 hsh1 hbd1 hsh2 hbd2)
  obtain ⟨s3, h3, hut'⟩ := spec_exists
    (swap_utinv hP s G hM hU hm1 hm2 hAne c1 c2 he1 he2 hsh1 hut1 hsh2 hut2)
  rw [h1] at h2 h3
  have e := eq_of_ok_eq h2
  have e3 := eq_of_ok_eq h3
  subst e e3
  rw [h1, WP.spec_ok]
  obtain ⟨σ', G', hsw, hG', hR', hV', hM', hC'⟩ := hpost
  exact ⟨σ', G', hsw, hR', hV', hM', hC', by rw [hG']; exact hinv, by rw [hG']; exact hut'⟩

end

section
variable {S A : Type} {st : machine.Store S} [L : P1.LawfulStore st] {ar : machine.Arch A}

/-- **`cdt::empty_slot` refines `empty_slot` and keeps `MdbInv` and `UtInv`.** -/
theorem empty_full_ut (th : TypedHeap) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G) (hU : UtInv (L.mem s) G)
    {px : U64} {rx : Nat} (hpx : th px = some (.cnode rx)) {idx : List Bool} (hl : idx.length = rx)
    {c : capability.Cap} (hc : capAt (L.mem s) (cslotAddr (px.bv, idx)) = ok c) (hcn : c ≠ .Null) :
    cdt.empty_slot st ar s a (cslotAddr (px.bv, idx)) .Null ⦃ r => r.2 = a ∧
      ∃ σ' G', Fl4Spec.emptySlot (Z := Unit) (px.bv, idx) .nullCap σ = ({((), σ')}, False) ∧
        StateRel th (L.mem r.1) σ' ∧ SlotsValid th (L.mem r.1) ∧ MdbLinks th (L.mem r.1) G' ∧
        CdtRel th (L.mem r.1) σ' G' ∧ MdbInv (L.mem r.1) G' ∧ UtInv (L.mem r.1) G' ⦄ := by
  have hAx : AbsSlot th (px.bv, idx) := ⟨px, rfl, Or.inl (by simpa [hl] using hpx)⟩
  have hxm := (hM.members _).2 ⟨hAx.isSlot, c, hc, hcn⟩
  obtain ⟨r1, h1, hpost⟩ := spec_exists (empty_slot_refines (ar := ar) th s a σ G hR hV hP hM hC hpx hl hc hcn)
  obtain ⟨r2, h2, hinv⟩ := spec_exists (empty_slot_mdbinv (ar := ar) hP s a G hM hI hxm hc hcn)
  obtain ⟨r3, h3, hut'⟩ := spec_exists (empty_slot_utinv (ar := ar) hP s a G hM hU hxm hc hcn)
  rw [h1] at h2 h3
  have e := eq_of_ok_eq h2
  have e3 := eq_of_ok_eq h3
  subst e e3
  rw [h1, WP.spec_ok]
  obtain ⟨hra, σ', G', hes, hR', hV', hM', hC', hG'⟩ := hpost
  exact ⟨hra, σ', G', hes, hR', hV', hM', hC', by rw [hG']; exact hinv, by rw [hG']; exact hut'⟩

end



section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`delete(slot, true)` refines l4v `cap_delete slot` and keeps `MdbInv` and `UtInv`** for a CNode
slot that is empty or holds a trivially finalised cap (`TrivKind`): FL4
returns `Ok`, and the state is related to the spec's single outcome. -/
theorem delete_full_ut (th : TypedHeap) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G) (hU : UtInv (L.mem s) G)
    {px : U64} {rx : Nat} (hpx : th px = some (.cnode rx)) {idx : List Bool} (hl : idx.length = rx)
    {c : capability.Cap} (hc : capAt (L.mem s) (cslotAddr (px.bv, idx)) = ok c)
    (ht : c = .Null ∨ ∃ fin, cdt.is_final_capability st s (cslotAddr (px.bv, idx)) = ok fin ∧ TrivKind σ c fin) :
    cdt.delete st arI s a (cslotAddr (px.bv, idx)) true ⦃ r => r.1 = .Ok () ∧
      ∃ σ' G', (Fl4Spec.capDelete (Z := Unit) (px.bv, idx)).run σ = ({(.ok (), σ')}, False) ∧
        StateRel th (L.mem r.2.1) σ' ∧ SlotsValid th (L.mem r.2.1) ∧ MdbLinks th (L.mem r.2.1) G' ∧
        CdtRel th (L.mem r.2.1) σ' G' ∧ MdbInv (L.mem r.2.1) G' ∧ UtInv (L.mem r.2.1) G' ⦄ := by
  obtain ⟨c', a', hc', hca, hg⟩ := hR.slot_cap (Z := Unit) (sl := (px.bv, idx)) rfl (by rw [hl]; exact hpx)
  rw [hc] at hc'
  have : c' = c := by simpa using hc'.symm
  subst this
  rw [hca.abs] at hg
  unfold cdt.delete
  simp only [↓reduceIte]
  rw [finalise_imm_triv arI σ s a _ c' hc ht]
  simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
  rcases ht with rfl | ⟨fin, hfin, htk⟩
  · -- empty slot: nothing changes
    rw [empty_slot_null arI s a _ hc]
    simp only [bind_ok, uncurry_apply_pair]
    rw [WP.spec_ok]
    have he : Fl4Spec.emptySlot (Z := Unit) (px.bv, idx) .nullCap σ = ({((), σ)}, False) := by
      unfold Fl4Spec.emptySlot
      rw [nd_bind_single hg]; simp [absCap]
    exact ⟨rfl, σ, G, capDelete_triv _ σ σ hg (Or.inl rfl) he, hR, hV, hM, hC, hI, hU⟩
  · have hcn : c' ≠ .Null := by intro e; subst e; simp [TrivKind] at htk
    obtain ⟨⟨s2, a2⟩, he2, ha2, σ', G', hes, hR', hV', hM', hC', hI', hU'⟩ :=
      spec_exists (empty_full_ut (ar := arI) th s a σ G hR hV hP hM hC hI hU hpx hl hc hcn)
    simp only at ha2 hR' hV' hM' hC' hI' hU'
    rw [he2]
    simp only [bind_ok, uncurry_apply_pair]
    rw [WP.spec_ok]
    exact ⟨rfl, σ', G', capDelete_triv _ σ σ' hg (Or.inr ⟨c', fin, rfl, hcn, htk⟩) hes, hR', hV', hM', hC', hI', hU'⟩

end

end

end Fl4Proofs.P3
