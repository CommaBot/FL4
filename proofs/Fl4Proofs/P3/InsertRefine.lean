/-
P3 (DESIGN.md §9), CSpace: **`cdt::insert` refines l4v `cap_insert`**
(nondeterministic spec, `Z = Unit`), for two CNode slots of the typed heap.

`insert_refines`: from related states (`StateRel`, `SlotsValid`, `Placed`,
`MdbLinks` with ghost `G`, `CdtRel`), with `src` holding a non-null cap,
`dest` null, and a new cap `c` related to the spec's `a` (`CapRel`, valid,
fitting its encoding, non-null, of the source's kind if badged), FL4's
`insert c src dest` ends in a state related to the spec's single outcome of
`cap_insert a src dest`, with the ghost tree updated by inserting `dest`
after `src` (child of `src` when `should_be_parent_of`, else its sibling).

Extra hypothesis `hsib` (an invariant of the spec's reachable states, to be
proved in P1/P3 later): when the new cap is not to be `src`'s child, `src`
has no descendants. FL4 (like seL4's `cteInsert`) always links `dest` right
after `src`, which is only a correct layout of the tree if this holds.
-/
import Fl4Proofs.P3.Insert
import Fl4Proofs.P3.MdbInsert
import Fl4Proofs.P3.InsertSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

theorem StateRel.of_kheap {Z : Type} {th : TypedHeap} {mem : U64 → U64} {σ σ' : Fl4Spec.State Z}
    (h : StateRel th mem σ) (hk : σ'.kheap = σ.kheap) : StateRel th mem σ' := by
  refine ⟨fun p r hp => ?_, fun t ht => ?_⟩
  · rw [hk]; exact h.cnode p r hp
  · rw [hk]; exact h.tcb t ht

theorem SlotRel.cap_eq {mem : U64 → U64} {a : U64} {o : Option Fl4Spec.Cap} {c : capability.Cap}
    (h : SlotRel mem a o) (hc : capAt mem a = ok c) : ∃ ac, o = some ac ∧ CapRel c ac := by
  obtain ⟨c', ac, hc', ho, hr⟩ := h
  rw [hc] at hc'
  have : c = c' := by simpa using hc'
  subst this; exact ⟨ac, ho, hr⟩

/-- The ghost tree after inserting `dest` after `src` (as `src`'s child iff `b`). -/
def insG (G : MdbGhost) (src dest : U64) (b : Bool) : MdbGhost :=
  ⟨G.chains.map (Mdb.insAfter src dest), Function.update G.par dest (if b then some src else G.par src)⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- `insert_refines` with `hsib` assumed only for the outcome (the
computation itself terminates regardless). -/
theorem insert_refines' (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    {ps pd : U64} {rs rd : Nat} (hps : th ps = some (.cnode rs)) (hpd : th pd = some (.cnode rd))
    {idxs idxd : List Bool} (hls : idxs.length = rs) (hld : idxd.length = rd)
    {srcC : capability.Cap} (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok srcC)
    (hsnn : srcC ≠ .Null)
    (hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null)
    (c : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel c a) (hcv : CapValid th c) (he : EncWf c)
    (hcnn : c ≠ .Null) (hk : SameBadgeKind c srcC) :
    cdt.insert st s c (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)) ⦃ s' =>
      (¬ Fl4Spec.shouldBeParentOf (absCap srcC) (σ.isOriginalCap (ps.bv, idxs)) a
        (decide (Fl4Spec.isCapRevocable a (absCap srcC))) →
        ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (ps.bv, idxs))) →
      ∃ σ' G', Fl4Spec.capInsert (Z := Unit) a (ps.bv, idxs) (pd.bv, idxd) σ = ({((), σ')}, False) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧ MdbLinks th (L.mem s') G' ∧
        CdtRel th (L.mem s') σ' G' ∧
        G' = insG G (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd))
          (decide (Fl4Spec.shouldBeParentOf (absCap srcC) (σ.isOriginalCap (ps.bv, idxs)) a
            (decide (Fl4Spec.isCapRevocable a (absCap srcC))))) ⦄ := by
  -- the two slots
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
  obtain ⟨csd, hkd, hwfd, hsd⟩ := hR.cnode pd rd hpd
  obtain ⟨srcA, hsA, hsrel⟩ := (hss idxs hls).cap_eq hsrcC
  have hsrcA : srcA = absCap srcC := hsrel.abs
  subst hsrcA
  obtain ⟨dA, hdA, hdrel⟩ := (hsd idxd hld).cap_eq hdst
  have hdA' : dA = .nullCap := by rw [hdrel.abs]; rfl
  subst hdA'
  have hgs : Fl4Spec.getCap (Z := Unit) (ps.bv, idxs) σ = ({(absCap srcC, σ)}, False) := getCap_cnode hks hwfs hsA
  have hgd : Fl4Spec.getCap (Z := Unit) (pd.bv, idxd) σ = ({(.nullCap, σ)}, False) := getCap_cnode hkd hwfd hdA
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
  obtain ⟨csd1, hkd1, hwfd1, -⟩ := hR1.cnode pd rd hpd
  have hdsp : IsSlotAt th pd (blVal 0 idxd) := Or.inl ⟨rd, hpd, hld ▸ blVal_lt idxd⟩
  have hdestEq : dest = slotOf pd (blVal 0 idxd) := slotAddr_ofBl pd idxd
  have hcap' : ∀ x, IsSlot th x → capAt (L.mem s') x = if x = dest then ok c else capAt mem1 x := by
    intro x hx
    rw [hW.capAt' hx he hes hsrcC, hcap1 x hx]
  obtain ⟨hR2, hV2⟩ := StateRel.update_cnode_slot hR1 hV1 hP hpd hkd1 hwfd1 hld hca hcv
    (by rw [← hdestEq]; exact hcap')
  have h2 := setCap_cnode (Z := Unit) a hkd1 hwfd1 hld
  set σ2 := setCnodeSlot σ1 pd.bv rd csd1 idxd a
  have hins := capInsert_eq hgs hgd h1 h2 (by simp [σ2, setCnodeSlot, hio1]) (by simp [σ2, setCnodeSlot, hcdt1])
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

theorem insert_refines (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    {ps pd : U64} {rs rd : Nat} (hps : th ps = some (.cnode rs)) (hpd : th pd = some (.cnode rd))
    {idxs idxd : List Bool} (hls : idxs.length = rs) (hld : idxd.length = rd)
    {srcC : capability.Cap} (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok srcC)
    (hsnn : srcC ≠ .Null)
    (hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null)
    (c : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel c a) (hcv : CapValid th c) (he : EncWf c)
    (hcnn : c ≠ .Null) (hk : SameBadgeKind c srcC)
    (hsib : ¬ Fl4Spec.shouldBeParentOf (absCap srcC) (σ.isOriginalCap (ps.bv, idxs)) a
        (decide (Fl4Spec.isCapRevocable a (absCap srcC))) →
      ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (ps.bv, idxs))) :
    cdt.insert st s c (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)) ⦃ s' =>
      ∃ σ' G', Fl4Spec.capInsert (Z := Unit) a (ps.bv, idxs) (pd.bv, idxd) σ = ({((), σ')}, False) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧ MdbLinks th (L.mem s') G' ∧
        CdtRel th (L.mem s') σ' G' ∧
        G' = insG G (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd))
          (decide (Fl4Spec.shouldBeParentOf (absCap srcC) (σ.isOriginalCap (ps.bv, idxs)) a
            (decide (Fl4Spec.isCapRevocable a (absCap srcC))))) ⦄ :=
  WP.spec_mono (insert_refines' th s σ G hR hV hP hM hC hps hpd hls hld hsrcC hsnn hdst c a hca hcv he hcnn hk)
    (fun _ h => h hsib)

end

end

end Fl4Proofs.P3
