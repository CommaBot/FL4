/-
P3 (DESIGN.md §9), CSpace: **`FinM` through the insertion of a frame alias**
(DeriveSubframe, l4h 0029). A 4 KiB frame cap made of a page of a large
frame cap overlaps the large frame cap (at offset 0) and the other aliases
of its page, with different object keys: `FinM.key` and `FinM.fnest`
exempt frame–frame pairs (frames are never finalised: `NeedsFin` excludes
them), so the insertion keeps `FinM` when every cap the alias overlaps is a
frame cap in the chain of the cap it is inserted after (`hov`).

`FinM.insert_frame` is the ghost-level step; `insert_frame_finM` is
`cdt::insert` of the alias, and `insert_frame_fin` adds `KTyped` (the
spec's `cap_insert` keeps the CNodes and TCBs).
-/
import Fl4Proofs.P3.FinOps
import Fl4Proofs.P3.UntypedMdb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

theorem isZb_of_frame {c : capability.Cap} (h : isFrame c = true) : isZb c = false := by
  cases c <;> simp_all [isFrame, isZb]

/-- From a frame cap, `same_region_as` only with a frame cap. -/
theorem srB_frame_frame {a b : capability.Cap} (ha : isFrame a = true) (h : srB a b = true) : isFrame b = true := by
  cases a <;> simp [isFrame] at ha
  have := (srB_frame_in h).1
  cases b <;> simp_all [isFr, isFrame]

theorem mem_insAfter' {ch : List U64} {src dest z : U64} (hdest : dest ∉ ch) (hz : z ∈ Mdb.insAfter src dest ch) :
    (z = dest ∧ src ∈ ch) ∨ (z ∈ ch ∧ z ≠ dest) := by
  by_cases hs : src ∈ ch
  · rcases (mem_insAfter hs).1 hz with h | h
    · exact Or.inl ⟨h, hs⟩
    · exact Or.inr ⟨h, fun e => hdest (e ▸ h)⟩
  · rw [Mdb.insAfter_of_not_mem hs] at hz
    exact Or.inr ⟨hz, fun e => hdest (e ▸ hz)⟩

/-- **A frame alias inserted after `src`**: `FinM` kept when every cap of
the MDB the alias overlaps is a frame cap in `src`'s chain, `src`'s cap kept
alike, the others unchanged. -/
theorem FinM.insert_frame {mem mem' : U64 → U64} {G : MdbGhost} (hF : FinM mem G) (hndG : G.chains.flatten.Nodup)
    {src dest : U64} (hsrc : src ∈ G.chains.flatten) (hdest : dest ∉ G.chains.flatten) (b : Bool)
    (hfd : isFrame (capV mem' dest) = true)
    (hov : ∀ w ∈ G.chains.flatten, Ovl (absCap (capV mem' dest)) (absCap (capV mem w)) →
      isFrame (capV mem w) = true ∧ ∃ ch ∈ G.chains, src ∈ ch ∧ w ∈ ch)
    (hcs : CapSim (capV mem' src) (capV mem src))
    (hcap : ∀ z ∈ G.chains.flatten, z ≠ src → capV mem' z = capV mem z) : FinM mem' (insG G src dest b) := by
  have hsim : ∀ z ∈ G.chains.flatten, CapSim (capV mem' z) (capV mem z) := by
    intro z hz
    by_cases e : z = src
    · subst e; exact hcs
    · rw [hcap z hz e]; exact CapSim.refl _
  have hmemf : ∀ z, z ∈ (insG G src dest b).chains.flatten ↔ z = dest ∨ z ∈ G.chains.flatten := fun z =>
    mem_flatten_ins hsrc
  have hovl : ∀ z ∈ G.chains.flatten, ∀ w ∈ G.chains.flatten,
      Ovl (absCap (capV mem' z)) (absCap (capV mem' w)) → Ovl (absCap (capV mem z)) (absCap (capV mem w)) := by
    intro z hz w hw h; unfold Ovl at h ⊢; rwa [(hsim z hz).refs, (hsim w hw).refs] at h
  have hovd : ∀ w ∈ G.chains.flatten, Ovl (absCap (capV mem' dest)) (absCap (capV mem' w)) →
      isFrame (capV mem' w) = true ∧ ∃ ch ∈ G.chains, src ∈ ch ∧ w ∈ ch := by
    intro w hw h
    have h' : Ovl (absCap (capV mem' dest)) (absCap (capV mem w)) := by
      unfold Ovl at h ⊢; rwa [(hsim w hw).refs] at h
    obtain ⟨h1, h2⟩ := hov w hw h'
    exact ⟨by rw [(hsim w hw).fr]; exact h1, h2⟩
  have hdz : isZb (capV mem' dest) = false := isZb_of_frame hfd
  refine ⟨fun ch1 hch1 ch2 hch2 x hx y hy hxy => ?_, fun x hx y hy hxy hov' hzx hzy hff => ?_,
    fun x hx y hy hxy hfx hfy hsr => ?_, fun x hx y hy hxy hzx hov' => ?_⟩
  · -- conn
    obtain ⟨c1, hc1, rfl⟩ := List.mem_map.1 hch1
    obtain ⟨c2, hc2, rfl⟩ := List.mem_map.1 hch2
    have hd1 : dest ∉ c1 := fun h => hdest (List.mem_flatten.2 ⟨c1, hc1, h⟩)
    have hd2 : dest ∉ c2 := fun h => hdest (List.mem_flatten.2 ⟨c2, hc2, h⟩)
    have hm1 : ∀ z ∈ c1, z ∈ G.chains.flatten := fun z hz => List.mem_flatten.2 ⟨c1, hc1, hz⟩
    have hm2 : ∀ z ∈ c2, z ∈ G.chains.flatten := fun z hz => List.mem_flatten.2 ⟨c2, hc2, hz⟩
    -- the chain of `src`
    have hsrcch : ∀ c ∈ G.chains, ∀ w ∈ c, (∃ ch ∈ G.chains, src ∈ ch ∧ w ∈ ch) → src ∈ c := by
      rintro c hc w hw ⟨ch, hch, hs, hw'⟩
      rw [chain_unique hndG hc hch hw hw']; exact hs
    rcases mem_insAfter' hd1 hx with ⟨rfl, hs1⟩ | ⟨hx1, hxd⟩ <;>
      rcases mem_insAfter' hd2 hy with ⟨rfl, hs2⟩ | ⟨hy2, hyd⟩
    · rw [chain_unique hndG hc1 hc2 hs1 hs2]
    · obtain ⟨-, hch⟩ := hovd y (hm2 y hy2) hxy
      rw [chain_unique hndG hc1 hc2 hs1 (hsrcch c2 hc2 y hy2 hch)]
    · obtain ⟨-, hch⟩ := hovd x (hm1 x hx1) hxy.symm
      rw [chain_unique hndG hc1 hc2 (hsrcch c1 hc1 x hx1 hch) hs2]
    · rw [hF.conn c1 hc1 c2 hc2 x hx1 y hy2 (hovl x (hm1 x hx1) y (hm2 y hy2) hxy)]
  · -- key
    rcases (hmemf x).1 hx with rfl | hx0 <;> rcases (hmemf y).1 hy with rfl | hy0
    · exact absurd rfl hxy
    · exact absurd ⟨hfd, (hovd y hy0 hov').1⟩ hff
    · exact absurd ⟨(hovd x hx0 hov'.symm).1, hfd⟩ hff
    · rw [(hsim x hx0).key, (hsim y hy0).key]
      exact hF.key x hx0 y hy0 hxy (hovl x hx0 y hy0 hov') (by rw [← (hsim x hx0).zb]; exact hzx)
        (by rw [← (hsim y hy0).zb]; exact hzy) (by rw [← (hsim x hx0).fr, ← (hsim y hy0).fr]; exact hff)
  · -- fnest
    rcases (hmemf x).1 hx with rfl | hx0 <;> rcases (hmemf y).1 hy with rfl | hy0
    · exact absurd rfl hxy
    · unfold srM at hsr; rw [srB_frame_frame hfx hsr] at hfy; cases hfy
    · rw [hfd] at hfy; cases hfy
    · rw [(hsim x hx0).key, (hsim y hy0).key]
      refine hF.fnest x hx0 y hy0 hxy (by rw [← (hsim x hx0).fr]; exact hfx) (by rw [← (hsim y hy0).fr]; exact hfy) ?_
      unfold srM at hsr ⊢; rw [(hsim x hx0).srl, (hsim y hy0).srr] at hsr; exact hsr
  · -- zfin
    rcases (hmemf x).1 hx with rfl | hx0 <;> rcases (hmemf y).1 hy with rfl | hy0
    · exact absurd rfl hxy
    · rw [hdz] at hzx; cases hzx
    · rw [isZb_of_frame (hovd x hx0 hov'.symm).1] at hzx; cases hzx
    · exact hF.zfin x hx0 y hy0 hxy (by rw [← (hsim x hx0).zb]; exact hzx) (hovl x hx0 y hy0 hov')

section
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`cdt::insert` of a frame alias keeps `FinM`**: a frame cap `c` inserted
after a frame cap's slot `src`, every cap of the MDB that `c` overlaps a
frame cap in `src`'s chain. -/
theorem insert_frame_finM (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    (hF : FinM (L.mem s) G) {src dest : U64} (hsrc : src ∈ G.chains.flatten)
    (hd : IsSlot th dest) (hdest : dest ∉ G.chains.flatten) {srcC : capability.Cap}
    (hsrcC : capAt (L.mem s) src = ok srcC) (hfs : isFrame srcC = true)
    (c : capability.Cap) (he : EncWf c) (hfc : isFrame c = true)
    (hov : ∀ w ∈ G.chains.flatten, Ovl (absCap c) (absCap (capV (L.mem s) w)) →
      isFrame (capV (L.mem s) w) = true ∧ ∃ ch ∈ G.chains, src ∈ ch ∧ w ∈ ch) :
    cdt.insert st s c src dest ⦃ s' => ∀ b, FinM (L.mem s') (insG G src dest b) ⦄ := by
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
  have hful : fullF srcC c = none := by
    cases srcC <;> simp [isFrame] at hfs; rfl
  apply WP.spec_mono (insert_mem hP s c src dest hs hd hne srcC hsrcC hnx)
  intro s' hW b
  have hcap : ∀ a, IsSlot th a → capV (L.mem s') a =
      if a = dest then c else if a = src then (fullF srcC c).getD srcC else capV (L.mem s) a := by
    intro a ha
    have := hW.capAt' ha he hes hsrcC
    rw [capAt_capV] at this
    by_cases h1 : a = dest
    · subst h1; simp only [↓reduceIte] at this ⊢; simpa using this
    · by_cases h2 : a = src
      · subst h2; simp only [h1, ↓reduceIte] at this ⊢; simpa using this
      · simp only [h1, h2, ↓reduceIte] at this ⊢; rw [capAt_capV] at this; simpa using this
  have hcd : capV (L.mem s') dest = c := by rw [hcap dest hd, if_pos rfl]
  refine hF.insert_frame hM.tree.nodup hsrc hdest b (by rw [hcd]; exact hfc) (by rw [hcd]; exact hov) ?_ ?_
  · rw [hcap src hs, if_neg hne, if_pos rfl, hful, hcv]; exact CapSim.refl _
  · intro z hz hzs
    have hzd : z ≠ dest := fun e => hdest (e ▸ hz)
    rw [hcap z (hslot z hz), if_neg hzd, if_neg hzs]

/-- **`FinInv` after a frame alias's `cdt::insert`**, against the spec's
`cap_insert` (`KTyped` from `capInsert_nks`). -/
theorem insert_frame_fin (hP : Placed th) (s : S) (σ σ' : Fl4Spec.State Unit) (G : MdbGhost)
    (hM : MdbLinks th (L.mem s) G) (hFI : FinInv th (L.mem s) σ G) {src dest : U64} (hsrc : src ∈ G.chains.flatten)
    (hd : IsSlot th dest) (hdest : dest ∉ G.chains.flatten) {srcC : capability.Cap}
    (hsrcC : capAt (L.mem s) src = ok srcC) (hfs : isFrame srcC = true)
    (c : capability.Cap) (he : EncWf c) (hfc : isFrame c = true)
    (hov : ∀ w ∈ G.chains.flatten, Ovl (absCap c) (absCap (capV (L.mem s) w)) →
      isFrame (capV (L.mem s) w) = true ∧ ∃ ch ∈ G.chains, src ∈ ch ∧ w ∈ ch)
    (a : Fl4Spec.Cap) (ssl dsl : Fl4Spec.CslotPtr) (y : Unit × Fl4Spec.State Unit)
    (hy : y ∈ (Fl4Spec.capInsert (Z := Unit) a ssl dsl σ).1) (hy2 : y.2 = σ') :
    cdt.insert st s c src dest ⦃ s' => ∀ b, FinInv th (L.mem s') σ' (insG G src dest b) ⦄ := by
  refine WP.spec_mono (insert_frame_finM hP s G hM hFI.fm hsrc hd hdest hsrcC hfs c he hfc hov) ?_
  intro s' h b
  exact ⟨hFI.kt.sub (by rw [← hy2]; exact capInsert_nks _ _ _ σ y hy), h b⟩

end

end

end Fl4Proofs.P3
