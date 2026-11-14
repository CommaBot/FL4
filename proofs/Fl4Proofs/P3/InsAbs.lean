/-
P3 (DESIGN.md §9), CSpace: **`cdt::insert` into any slot of the typed heap**
(`insert_refines_abs`): `insert_refines'` with the destination a CNode or
TCB slot (`AbsSlot`), the source a CNode slot. TCB ThreadControl installs
caps into TCB slots.
-/
import Fl4Proofs.P3.InsertRefine
import Fl4Proofs.P3.DelAbs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

theorem eq_of_ok_eq' {α : Type} {a b : α} (h : (ok a : Result α) = ok b) : a = b := by simpa using h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem insert_refines_abs (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs))
    {idxs : List Bool} (hls : idxs.length = rs) {dsl : Fl4Spec.CslotPtr} (hAd : AbsSlot th dsl)
    {srcC : capability.Cap} (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok srcC)
    (hsnn : srcC ≠ .Null)
    (hdst : capAt (L.mem s) (cslotAddr dsl) = ok .Null)
    (c : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel c a) (hcv : CapValid th c) (he : EncWf c)
    (hcnn : c ≠ .Null) (hk : SameBadgeKind c srcC) :
    cdt.insert st s c (cslotAddr (ps.bv, idxs)) (cslotAddr dsl) ⦃ s' =>
      (¬ Fl4Spec.shouldBeParentOf (absCap srcC) (σ.isOriginalCap (ps.bv, idxs)) a
        (decide (Fl4Spec.isCapRevocable a (absCap srcC))) →
        ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (ps.bv, idxs))) →
      ∃ σ' G', Fl4Spec.capInsert (Z := Unit) a (ps.bv, idxs) dsl σ = ({((), σ')}, False) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧ MdbLinks th (L.mem s') G' ∧
        CdtRel th (L.mem s') σ' G' ∧
        G' = insG G (cslotAddr (ps.bv, idxs)) (cslotAddr dsl)
          (decide (Fl4Spec.shouldBeParentOf (absCap srcC) (σ.isOriginalCap (ps.bv, idxs)) a
            (decide (Fl4Spec.isCapRevocable a (absCap srcC))))) ⦄ := by
  -- the two slots
  have hAs : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  set src := cslotAddr (ps.bv, idxs) with hsrcdef
  set dest := cslotAddr dsl with hdestdef
  have hs : IsSlot th src := hAs.isSlot
  have hd : IsSlot th dest := hAd.isSlot
  have hne : src ≠ dest := by
    intro e; rw [e, hdst] at hsrcC
    have : capability.Cap.Null = srcC := by simpa using hsrcC
    exact hsnn this.symm
  have hes : EncWf srcC := by rw [capAt_words] at hsrcC; exact decode_encWf hsrcC
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
  -- abstract caps
  obtain ⟨css, hks, hwfs, hss⟩ := hR.cnode ps rs hps
  obtain ⟨srcA, hsA, hsrel⟩ := (hss idxs hls).cap_eq hsrcC
  have hsrcA : srcA = absCap srcC := hsrel.abs
  subst hsrcA
  have hgs : Fl4Spec.getCap (Z := Unit) (ps.bv, idxs) σ = ({(absCap srcC, σ)}, False) := getCap_cnode hks hwfs hsA
  have hgd : Fl4Spec.getCap (Z := Unit) dsl σ = ({(.nullCap, σ)}, False) := by
    obtain ⟨c0, a0, hc0, hca0, hg0⟩ := hR.abs_cap hAd
    rw [hdst] at hc0; cases eq_of_ok_eq' hc0
    rw [hg0, hca0.abs]; rfl
  apply WP.spec_mono (insert_mem hP s c src dest hs hd hne srcC hsrcC hnx)
  intro s' hW hsib
  -- the intermediate state after `set_untyped_cap_as_full`
  obtain ⟨σ1, mem1, h1, hR1, hV1, hcap1, hk1, hio1, hcdt1⟩ : ∃ σ1 mem1,
      Fl4Spec.setUntypedCapAsFull (Z := Unit) (absCap srcC) a (ps.bv, idxs) σ = ({((), σ1)}, False) ∧
      StateRel th mem1 σ1 ∧ SlotsValid th mem1 ∧
      (∀ x, IsSlot th x → capAt mem1 x = if x = src then ok ((fullF srcC c).getD srcC) else capAt (L.mem s) x) ∧
      True ∧ σ1.isOriginalCap = σ.isOriginalCap ∧ σ1.cdt = σ.cdt := by
    cases hf : fullF srcC c with
    | none =>
      refine ⟨σ, L.mem s, setUntyped_skip ?_, hR, hV, ?_, trivial, rfl, rfl⟩
      · rw [hca.abs, fullF_spec, hf]; simp
      · intro x hx; by_cases h : x = src
        · subst h; simp [hsrcC]
        · simp [h]
    | some c' =>
      obtain ⟨hrel', he', hnn'⟩ := fullF_some hf hes
      have hcond := (fullF_spec srcC c).2 (by simp [hf])
      rw [← hca.abs] at hcond
      have hsp : IsSlotAt th ps (blVal 0 idxs) := Or.inl ⟨rs, hps, hls ▸ blVal_lt idxs⟩
      have hsrcEq : src = slotOf ps (blVal 0 idxs) := slotAddr_ofBl ps idxs
      have hcapw : ∀ x, IsSlot th x → capAt (L.mem (wrCap (L := L) s src c')) x =
          if x = src then ok c' else capAt (L.mem s) x := by
        intro x hx
        by_cases h : x = src
        · subst h
          have f := hs.fit hP
          rw [if_pos rfl]
          apply capAt_wr2_self _ _ _ he' (by rw [hsrcEq]; exact hsp.al hP) (by rw [hsrcEq]; exact hsp.al8 hP)
          rw [wa8_val (by omega)]; omega
        · rw [if_neg h]
          obtain ⟨q, j, hq, rfl⟩ := hx
          rw [hsrcEq] at h ⊢
          exact capAt_other_slot hP s hsp hq (fun ⟨e1, e2⟩ => h (by rw [e1, e2])) _ _
      have hcv' : CapValid th c' := by
        cases srcC <;> cases c <;> simp [fullF] at hf
        obtain ⟨-, -, rfl⟩ := hf; trivial
      obtain ⟨hR1, hV1⟩ := StateRel.update_cnode_slot hR hV hP hps hks hwfs hls hrel' hcv'
        (by rw [← hsrcEq]; exact hcapw)
      refine ⟨_, _, ?_, hR1, hV1, ?_, trivial, rfl, rfl⟩
      · rw [setUntyped_full hcond, setCap_cnode _ hks hwfs hls]
      · intro x hx; rw [hcapw x hx]; simp [hf]
  -- the state after `set_cap` of the new cap
  have hcap' : ∀ x, IsSlot th x → capAt (L.mem s') x = if x = dest then ok c else capAt mem1 x := by
    intro x hx
    rw [hW.capAt' hx he hes hsrcC, hcap1 x hx]
  obtain ⟨σ2, h2, hR2, hV2, hσ2, -⟩ := StateRel.update_abs_slot hR1 hV1 hP hAd hca hcv hcap'
  have hins := capInsert_eq hgs hgd h1 h2 (by rw [hσ2]; exact hio1) (by rw [hσ2]; exact hcdt1)
  clear hσ2
  -- the tree
  set b := decide (Fl4Spec.shouldBeParentOf (absCap srcC) (σ.isOriginalCap (ps.bv, idxs)) a
    (decide (Fl4Spec.isCapRevocable a (absCap srcC))))
  have hcase : Mdb.InsCase G.par src (if b then some src else G.par src) := by
    cases hb : b
    · right; refine ⟨rfl, hsib (by simpa [b] using hb)⟩
    · left; rfl
  have hL : InsLinks th (L.mem s) (L.mem s') src dest := by
    refine ⟨fun x hx => hW.prevOf' hx hNs, fun x hx => hW.nextOf' hP hx hd hne hNc, ⟨c, ?_, hcnn⟩, ?_, ?_⟩
    · rw [hcap' dest hd]; simp
    · refine ⟨(fullF srcC c).getD srcC, ?_, ?_⟩
      · rw [hcap' src hs, hcap1 src hs]; simp [hne]
      · cases hf : fullF srcC c with
        | none => simpa using hsnn
        | some c' => simpa using (fullF_some hf hes).2.2
    · intro x hx hxd hxs
      rw [hcap' x hx, hcap1 x hx]; simp [hxd, hxs]
  refine ⟨_, _, hins, StateRel.of_kheap hR2 rfl, hV2, MdbLinks.insert hP hM hsrcm hd hdestm hcase hL, ?_, rfl⟩
  refine CdtRel.insert hP hC _ hAs hAd b (decide (Fl4Spec.isCapRevocable a (absCap srcC))) rfl rfl ?_
  intro x hx
  rw [hW.revOf' hx hne]
  by_cases h : x = dest
  · subst h
    simp only [↓reduceIte]
    rw [hca.abs]
    have := revF_spec c srcC hk
    cases hr : revF c srcC <;> simp_all
  · rw [if_neg h, if_neg h]

end

end

end Fl4Proofs.P3
