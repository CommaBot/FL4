/-
P3 (DESIGN.md §9), CSpace: **`cdt::move_cap` refines l4v `cap_move`**
(nondeterministic spec, `Z = Unit`), for two CNode slots of the typed heap.

`move_refines`: from related states, `src` holding a non-null cap, `dest`
null and a related new cap, FL4's `move_cap c src dest` ends in a state
related to the spec's single outcome of `cap_move a src dest`; the ghost tree
is renamed by the transposition of `src` and `dest` (`Mdb.conjPar`), which is
how the spec's `cdt` changes too.
-/
import Fl4Proofs.P3.Move
import Fl4Proofs.P3.MdbRename
import Fl4Proofs.P3.InsertRefine
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- The links after a move, as a renaming of `src` to `dest`. -/
theorem RenLinks.move {th : TypedHeap} (hP : Placed th) {mem mem' : U64 → U64} {G : MdbGhost}
    (hM : MdbLinks th mem G) {src dest : U64} (hsrc : src ∈ G.chains.flatten) (hd : IsSlot th dest)
    (hdest : dest ∉ G.chains.flatten)
    (hprev : ∀ a, IsSlot th a → prevOf mem' a = if a = dest then prevOf mem src else if a = src then 0#u64
      else if nextOf mem src ≠ 0#u64 ∧ a = nextOf mem src then dest else prevOf mem a)
    (hnext : ∀ a, IsSlot th a → nextOf mem' a = if a = dest then nextOf mem src else if a = src then 0#u64
      else if prevOf mem src ≠ 0#u64 ∧ a = prevOf mem src then dest else nextOf mem a)
    (hcap : ∀ a, IsSlot th a → a ≠ dest → a ≠ src → capAt mem' a = capAt mem a)
    (hcs : capAt mem' src = ok .Null) (hcd : ∃ c, capAt mem' dest = ok c ∧ c ≠ .Null) :
    RenLinks th mem mem' (Equiv.swap src dest) G := by
  have hslot : ∀ a, a ∈ G.chains.flatten → IsSlot th a := fun a h => ((hM.members a).1 h).1
  have hs := hslot src hsrc
  have hdne : ∀ x, x ∈ G.chains.flatten → x ≠ dest := fun x hx e => hdest (e ▸ hx)
  have hz : ∀ x, x ∈ G.chains.flatten → x ≠ 0#u64 := fun x hx => (hslot x hx).ne_zero hP
  have hsw0 : ∀ x, x ≠ src → x ≠ dest → Equiv.swap src dest x = x := fun x h1 h2 =>
    Equiv.swap_apply_of_ne_of_ne h1 h2
  have hne : src ≠ dest := hdne src hsrc
  -- `next`/`prev` of members are members or 0
  have hNm : ∀ a, a ∈ G.chains.flatten → nextOf mem a = 0#u64 ∨ nextOf mem a ∈ G.chains.flatten := by
    intro a ha; rcases hM.next_mem ha with h | ⟨h, -⟩ <;> [exact Or.inl h; exact Or.inr h]
  have hPm : ∀ a, a ∈ G.chains.flatten → prevOf mem a = 0#u64 ∨ prevOf mem a ∈ G.chains.flatten := by
    intro a ha
    by_cases h : prevOf mem a = 0#u64
    · exact Or.inl h
    · exact Or.inr (hM.prev_link ha h).1
  have hsw : ∀ y, (y = 0#u64 ∨ y ∈ G.chains.flatten) → y ≠ src → Equiv.swap src dest y = y := by
    intro y hy hys
    apply hsw0 y hys
    rcases hy with rfl | hy
    · exact (hd.ne_zero hP).symm
    · exact hdne y hy
  refine ⟨hsw0 _ (hz src hsrc).symm (hd.ne_zero hP).symm, ?_, ?_, ?_⟩
  · intro a ha
    by_cases has : a = src
    · subst has
      rw [Equiv.swap_apply_left, hnext dest hd, if_pos rfl]
      rcases hM.next_mem ha with h | ⟨h1, h2⟩
      · rw [h]; exact (hsw _ (Or.inl rfl) (hz _ ha).symm).symm
      · exact (hsw _ (Or.inr h1) h2).symm
    · rw [hsw0 a has (hdne a ha), hnext a (hslot a ha), if_neg (hdne a ha), if_neg has]
      by_cases hn : nextOf mem a = src
      · have hp := (hM.next_link ha (by rw [hn]; exact hz src hsrc)).2
        rw [hn] at hp
        rw [if_pos ⟨by rw [hp]; exact hz a ha, hp.symm⟩, hn, Equiv.swap_apply_left]
      · rw [hsw _ (hNm a ha) hn, if_neg]
        rintro ⟨h0, rfl⟩
        exact hn (hM.prev_link hsrc h0).2
  · intro a ha
    by_cases has : a = src
    · subst has
      rw [Equiv.swap_apply_left, hprev dest hd, if_pos rfl]
      rcases hPm a ha with h | h
      · rw [h]; exact (hsw _ (Or.inl rfl) (hz _ ha).symm).symm
      · refine (hsw _ (Or.inr h) ?_).symm
        intro e
        have := (hM.prev_link ha (by rw [e]; exact hz _ ha)).2
        rw [e] at this
        rcases hM.next_mem ha with h' | ⟨-, h'⟩
        · rw [h'] at this; exact hz a ha this.symm
        · exact h' this
    · rw [hsw0 a has (hdne a ha), hprev a (hslot a ha), if_neg (hdne a ha), if_neg has]
      by_cases hp : prevOf mem a = src
      · have hn := (hM.prev_link ha (by rw [hp]; exact hz src hsrc)).2
        rw [hp] at hn
        rw [if_pos ⟨by rw [hn]; exact hz a ha, hn.symm⟩, hp, Equiv.swap_apply_left]
      · rw [hsw _ (hPm a ha) hp, if_neg]
        rintro ⟨h0, rfl⟩
        exact hp (hM.next_link hsrc h0).2
  · intro x
    simp only [List.mem_map]
    by_cases hxd : x = dest
    · subst hxd
      refine ⟨fun _ => ⟨hd, hcd⟩, fun _ => ⟨src, hsrc, Equiv.swap_apply_left _ _⟩⟩
    · by_cases hxs : x = src
      · subst hxs
        refine ⟨?_, ?_⟩
        · rintro ⟨y, hy, he⟩
          have : y = dest := by
            have := congrArg (Equiv.swap x dest) he
            simpa using this
          exact absurd (this ▸ hy) hdest
        · rintro ⟨-, c, hc, hn⟩
          rw [hcs] at hc
          have : capability.Cap.Null = c := by simpa using hc
          exact absurd this.symm hn
      · have hiff : x ∈ G.chains.flatten ↔ IsSlot th x ∧ ∃ c, capAt mem' x = ok c ∧ c ≠ .Null := by
          rw [hM.members x]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [hcap x h1 hxd hxs]; exact h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← hcap x h1 hxd hxs]; exact h2⟩
        rw [← hiff]
        constructor
        · rintro ⟨y, hy, he⟩
          have hy' : y = x := by
            have := congrArg (Equiv.swap src dest) he
            simp only [Equiv.swap_apply_self] at this
            rw [this, hsw0 x hxs hxd]
          exact hy' ▸ hy
        · intro hx; exact ⟨x, hx, hsw0 x hxs hxd⟩

/-- The spec's CDT after a move, as a renaming of the ghost tree. -/
theorem CdtRel.move {Z : Type} {th : TypedHeap} (hP : Placed th) {mem mem' : U64 → U64}
    {σ σ' : Fl4Spec.State Z} {G : MdbGhost} (hC : CdtRel th mem σ G) (hM : MdbLinks th mem G)
    (chains' : List (List U64))
    {srcSl destSl : Fl4Spec.CslotPtr} (hs : AbsSlot th srcSl) (hd : AbsSlot th destSl)
    (hsrcm : cslotAddr srcSl ∈ G.chains.flatten) (hdestm : cslotAddr destSl ∉ G.chains.flatten)
    (hcdt : σ'.cdt = fun r =>
      if Function.update (Function.update σ.cdt destSl (σ.cdt srcSl)) srcSl none r = some srcSl then some destSl
      else Function.update (Function.update σ.cdt destSl (σ.cdt srcSl)) srcSl none r)
    (hio : σ'.isOriginalCap =
      Function.update (Function.update σ.isOriginalCap destSl (σ.isOriginalCap srcSl)) srcSl false)
    (hrev : ∀ a, IsSlot th a → revOf mem' a = if a = cslotAddr destSl then revOf mem (cslotAddr srcSl)
      else if a = cslotAddr srcSl then false else revOf mem a) :
    CdtRel th mem' σ' ⟨chains', Mdb.conjPar (Equiv.swap (cslotAddr srcSl) (cslotAddr destSl)) G.par⟩ := by
  have hne : srcSl ≠ destSl := by rintro rfl; exact hdestm hsrcm
  have hAne : (cslotAddr srcSl) ≠ (cslotAddr destSl) := fun h => hne (cslotAddr_inj hP hs hd h)
  have hpd : G.par (cslotAddr destSl) = none := by
    cases h : G.par (cslotAddr destSl) with
    | none => rfl
    | some b => exact absurd (hM.tree.par_mem _ _ h).1 hdestm
  have hnpd : ∀ z, G.par z ≠ some (cslotAddr destSl) := fun z h => hdestm (hM.tree.par_mem _ _ h).2
  have hnc : ∀ sl, σ.cdt sl ≠ some destSl := by
    intro sl h
    have hsl := (hC.cdt_slot sl _ h).1
    have := hC.cdt sl hsl; rw [h] at this
    exact hnpd _ (by simpa using this.symm)
  have hss : σ.cdt srcSl ≠ some srcSl := by
    intro h; have := hC.cdt srcSl hs; rw [h] at this
    exact hM.no_self_par (by simpa using this.symm)
  have hupd : ∀ r, Function.update (Function.update σ.cdt destSl (σ.cdt srcSl)) srcSl none r =
      if r = srcSl then none else if r = destSl then σ.cdt srcSl else σ.cdt r := by
    intro r
    by_cases h1 : r = srcSl
    · subst r; simp
    · by_cases h2 : r = destSl
      · subst r; simp [h1]
      · simp [h1, h2]
  have hpar_fix : ∀ q, G.par (cslotAddr srcSl) = some q → (Equiv.swap (cslotAddr srcSl) (cslotAddr destSl)) q = q := by
    intro q hq
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h; subst h; exact hM.no_self_par hq
    · intro h; subst h; exact hnpd _ hq
  have hcp : ∀ x, Mdb.conjPar (Equiv.swap (cslotAddr srcSl) (cslotAddr destSl)) G.par x = (G.par ((Equiv.swap (cslotAddr srcSl) (cslotAddr destSl)) x)).map (Equiv.swap (cslotAddr srcSl) (cslotAddr destSl)) := by
    intro x; simp [Mdb.conjPar, Equiv.symm_swap]
  have hfix : ∀ sl, AbsSlot th sl → sl ≠ srcSl → sl ≠ destSl → (Equiv.swap (cslotAddr srcSl) (cslotAddr destSl)) (cslotAddr sl) = cslotAddr sl := by
    intro sl hsl h1 h2
    exact Equiv.swap_apply_of_ne_of_ne (fun h => h1 (cslotAddr_inj hP hsl hs h))
      (fun h => h2 (cslotAddr_inj hP hsl hd h))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro sl hsl
    show Option.map cslotAddr (σ'.cdt sl) = Mdb.conjPar _ G.par (cslotAddr sl)
    rw [hcdt, hcp]; simp only [hupd]
    by_cases h1 : sl = srcSl
    · rw [h1]
      simp only [↓reduceIte, reduceCtorEq, Option.map_none, Equiv.swap_apply_left, hpd]
    · by_cases h2 : sl = destSl
      · rw [h2]
        simp only [hne.symm, ↓reduceIte, hss, Equiv.swap_apply_right]
        rw [hC.cdt srcSl hs]
        cases hq : G.par (cslotAddr srcSl) with
        | none => rfl
        | some q => simp [hpar_fix q hq]
      · simp only [h1, h2, ↓reduceIte, hfix sl hsl h1 h2]
        rw [← hC.cdt sl hsl]
        by_cases h3 : σ.cdt sl = some srcSl
        · simp [h3]
        · rw [if_neg h3]
          cases hq : σ.cdt sl with
          | none => rfl
          | some q =>
            have hq' := (hC.cdt_slot sl q hq).2
            have hqs : q ≠ srcSl := fun h => h3 (by rw [hq, h])
            have hqd : q ≠ destSl := fun h => hnc sl (by rw [hq, h])
            simp [hfix q hq' hqs hqd]
  · intro sl q hq
    rw [hcdt] at hq; simp only [hupd] at hq
    by_cases h1 : sl = srcSl
    · rw [h1] at hq; simp at hq
    · by_cases h2 : sl = destSl
      · rw [h2] at hq
        simp only [hne.symm, ↓reduceIte, hss] at hq
        exact ⟨h2 ▸ hd, (hC.cdt_slot _ _ hq).2⟩
      · simp only [h1, h2, ↓reduceIte] at hq
        by_cases h3 : σ.cdt sl = some srcSl
        · rw [if_pos h3] at hq; cases hq; exact ⟨(hC.cdt_slot _ _ h3).1, hd⟩
        · rw [if_neg h3] at hq; exact hC.cdt_slot _ _ hq
  · intro sl hsl
    rw [hio, hrev _ hsl.isSlot]
    by_cases h1 : sl = srcSl
    · rw [h1]; simp [hAne]
    · by_cases h2 : sl = destSl
      · rw [h2]; simp [hne.symm, hC.orig srcSl hs]
      · have hsA : cslotAddr sl ≠ (cslotAddr srcSl) := fun h => h1 (cslotAddr_inj hP hsl hs h)
        have hdA : cslotAddr sl ≠ (cslotAddr destSl) := fun h => h2 (cslotAddr_inj hP hsl hd h)
        simp only [Function.update_of_ne h1, Function.update_of_ne h2, hsA, hdA, ↓reduceIte]
        exact hC.orig sl hsl
  · intro a b hab
    change Mdb.conjPar _ G.par a = some b at hab
    rw [hcp] at hab
    simp only [Option.map_eq_some_iff] at hab
    obtain ⟨b0, hb0, -⟩ := hab
    obtain ⟨sl0, hsl0, he0⟩ := hC.par_slot _ _ hb0
    by_cases h1 : (Equiv.swap (cslotAddr srcSl) (cslotAddr destSl)) a = (cslotAddr srcSl)
    · have : a = cslotAddr destSl := by
        have := congrArg (Equiv.swap (cslotAddr srcSl) (cslotAddr destSl)) h1; simpa using this
      exact ⟨destSl, hd, this.symm⟩
    · by_cases h2 : (Equiv.swap (cslotAddr srcSl) (cslotAddr destSl)) a = (cslotAddr destSl)
      · rw [h2, hpd] at hb0; cases hb0
      · have ha1 : a ≠ (cslotAddr srcSl) := fun h => h2 (by rw [h]; simp)
        have ha2 : a ≠ (cslotAddr destSl) := fun h => h1 (by rw [h]; simp)
        exact ⟨sl0, hsl0, he0.trans (Equiv.swap_apply_of_ne_of_ne ha1 ha2)⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The caps after writing one slot. -/
theorem capAt_wrCap {th : TypedHeap} (hP : Placed th) (s : S) {y : U64} (hy : IsSlot th y)
    {c : capability.Cap} (he : EncWf c) {x : U64} (hx : IsSlot th x) :
    capAt (L.mem (wrCap (L := L) s y c)) x = if x = y then ok c else capAt (L.mem s) x := by
  obtain ⟨p, i, hi, rfl⟩ := hy
  by_cases h : x = slotOf p i
  · subst h
    have f := hi.fit hP
    rw [if_pos rfl]
    apply capAt_wr2_self _ _ _ he (hi.al hP) (hi.al8 hP)
    rw [wa8_val (by omega)]; omega
  · rw [if_neg h]
    obtain ⟨q, j, hq, rfl⟩ := hx
    exact capAt_other_slot hP s hi hq (fun ⟨e1, e2⟩ => h (by rw [e1, e2])) _ _

theorem move_refines (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    {ps pd : U64} {rs rd : Nat} (hps : th ps = some (.cnode rs)) (hpd : th pd = some (.cnode rd))
    {idxs idxd : List Bool} (hls : idxs.length = rs) (hld : idxd.length = rd)
    {srcC : capability.Cap} (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok srcC)
    (hsnn : srcC ≠ .Null)
    (hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null)
    (c : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel c a) (hcv : CapValid th c) (he : EncWf c)
    (hcnn : c ≠ .Null) :
    cdt.move_cap st s c (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)) ⦃ s' =>
      ∃ σ' G', Fl4Spec.capMove (Z := Unit) a (ps.bv, idxs) (pd.bv, idxd) σ = ({((), σ')}, False) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧ MdbLinks th (L.mem s') G' ∧
        CdtRel th (L.mem s') σ' G' ∧
        G' = renG G (Equiv.swap (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd))) ⦄ := by
  have hAs : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hAd : AbsSlot th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
  have hs : IsSlot th (cslotAddr (ps.bv, idxs)) := hAs.isSlot
  have hd : IsSlot th (cslotAddr (pd.bv, idxd)) := hAd.isSlot
  have hne : cslotAddr (ps.bv, idxs) ≠ cslotAddr (pd.bv, idxd) := by
    intro e; rw [e, hdst] at hsrcC
    have : capability.Cap.Null = srcC := by simpa using hsrcC
    exact hsnn this.symm
  have hsrcm : cslotAddr (ps.bv, idxs) ∈ G.chains.flatten := (hM.members _).2 ⟨hs, srcC, hsrcC, hsnn⟩
  have hdestm : cslotAddr (pd.bv, idxd) ∉ G.chains.flatten := by
    intro h; obtain ⟨-, c0, h0, hn⟩ := (hM.members _).1 h
    rw [hdst] at h0
    have : capability.Cap.Null = c0 := by simpa using h0
    exact hn this.symm
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hnx : nextOf (L.mem s) (cslotAddr (ps.bv, idxs)) = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) (cslotAddr (ps.bv, idxs))) ∧
        nextOf (L.mem s) (cslotAddr (ps.bv, idxs)) ≠ cslotAddr (pd.bv, idxd) ∧
        nextOf (L.mem s) (cslotAddr (ps.bv, idxs)) ≠ cslotAddr (ps.bv, idxs)) := by
    rcases hM.next_mem hsrcm with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, fun e => hdestm (e ▸ h1), h2⟩
  have hpv : prevOf (L.mem s) (cslotAddr (ps.bv, idxs)) = 0#u64 ∨
      (IsSlot th (prevOf (L.mem s) (cslotAddr (ps.bv, idxs))) ∧
        prevOf (L.mem s) (cslotAddr (ps.bv, idxs)) ≠ cslotAddr (pd.bv, idxd) ∧
        prevOf (L.mem s) (cslotAddr (ps.bv, idxs)) ≠ cslotAddr (ps.bv, idxs)) := by
    by_cases h0 : prevOf (L.mem s) (cslotAddr (ps.bv, idxs)) = 0#u64
    · exact Or.inl h0
    · obtain ⟨h1, h2⟩ := hM.prev_link hsrcm h0
      refine Or.inr ⟨hslot _ h1, fun e => hdestm (e ▸ h1), fun e => ?_⟩
      rw [e] at h2
      rcases hM.next_mem hsrcm with h | ⟨-, h⟩
      · rw [h] at h2; exact hs.ne_zero hP h2.symm
      · exact h h2
  have hNc : Canonical (nextOf (L.mem s) (cslotAddr (ps.bv, idxs))) := by
    rcases hnx with h | ⟨h, -, -⟩
    · rw [h]; exact canonical_zero
    · exact h.canonical hP
  obtain ⟨css, hks, hwfs, -⟩ := hR.cnode ps rs hps
  obtain ⟨csd, hkd, hwfd, -⟩ := hR.cnode pd rd hpd
  apply WP.spec_mono (move_mem hP s c _ _ hs hd hne hpv hnx)
  intro s' hW
  -- after `set_cap` of the new cap in `dest`
  have hdestEq : cslotAddr (pd.bv, idxd) = slotOf pd (blVal 0 idxd) := slotAddr_ofBl pd idxd
  have hsrcEq : cslotAddr (ps.bv, idxs) = slotOf ps (blVal 0 idxs) := slotAddr_ofBl ps idxs
  have hcap1 : ∀ x, IsSlot th x → capAt (L.mem (wrCap (L := L) s (cslotAddr (pd.bv, idxd)) c)) x =
      if x = slotOf pd (blVal 0 idxd) then ok c else capAt (L.mem s) x := by
    intro x hx; rw [capAt_wrCap hP s hd he hx, hdestEq]
  obtain ⟨hR1, hV1⟩ := StateRel.update_cnode_slot hR hV hP hpd hkd hwfd hld hca hcv hcap1
  have h1 := setCap_cnode (Z := Unit) a hkd hwfd hld
  set σ1 := setCnodeSlot σ pd.bv rd csd idxd a
  obtain ⟨css1, hks1, hwfs1, -⟩ := hR1.cnode ps rs hps
  have hcap2 : ∀ x, IsSlot th x → capAt (L.mem s') x =
      if x = slotOf ps (blVal 0 idxs) then ok .Null
      else capAt (L.mem (wrCap (L := L) s (cslotAddr (pd.bv, idxd)) c)) x := by
    intro x hx
    rw [hW.capAt' hx he hne, capAt_wrCap hP s hd he hx, ← hsrcEq]
    by_cases h1 : x = cslotAddr (pd.bv, idxd)
    · subst h1; simp [hne.symm]
    · by_cases h2 : x = cslotAddr (ps.bv, idxs)
      · subst h2; simp [h1, hne]
      · simp [h1, h2]
  obtain ⟨hR2, hV2⟩ := StateRel.update_cnode_slot hR1 hV1 hP hps hks1 hwfs1 hls
    (show CapRel .Null .nullCap from ⟨trivial, rfl⟩) trivial hcap2
  have h2 := setCap_cnode (Z := Unit) .nullCap hks1 hwfs1 hls
  have hmv := capMove_eq h1 h2 (by simp [setCnodeSlot, σ1]) (by simp [setCnodeSlot, σ1])
  refine ⟨_, ⟨G.chains.map (List.map (Equiv.swap (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)))),
    Mdb.conjPar (Equiv.swap (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd))) G.par⟩, hmv,
    StateRel.of_kheap hR2 rfl, hV2, MdbLinks.rename (e := Equiv.swap (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd))) hM ?_, ?_, rfl⟩
  · refine RenLinks.move hP hM hsrcm hd hdestm (fun x hx => hW.prevOf' hx hne)
      (fun x hx => hW.nextOf' hP hx hd hne hNc) ?_ ?_ ⟨c, ?_, hcnn⟩
    · intro x hx h1 h2; rw [hW.capAt' hx he hne]; simp [h1, h2]
    · rw [hW.capAt' hs he hne]; simp [hne]
    · rw [hW.capAt' hd he hne]; simp
  · exact CdtRel.move hP hC hM _ hAs hAd hsrcm hdestm rfl rfl (fun x hx => hW.revOf' hx hne)

end

end

end Fl4Proofs.P3
