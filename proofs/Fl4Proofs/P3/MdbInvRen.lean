/-
P3 (DESIGN.md §9), CSpace: `MdbInv` after renaming slots (`cdt::move_cap`,
`cdt::swap`): if the new contents at `e a` are those of `a` (caps up to
shape and badge, the same bits, renamed links), the invariant holds for
the renamed tree.
-/
import Fl4Proofs.P3.MdbInvEmp
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

theorem MdbInv.rename {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    (hI : MdbInv mem G) (e : U64 ≃ U64) (he0 : e 0#u64 = 0#u64)
    (hnext : ∀ a ∈ G.chains.flatten, nextOf mem' (e a) = e (nextOf mem a))
    (hcap : ∀ a ∈ G.chains.flatten,
      shape (capV mem' (e a)) = shape (capV mem a) ∧ badgeF (capV mem' (e a)) = badgeF (capV mem a))
    (hrev : ∀ a ∈ G.chains.flatten, revOf mem' (e a) = revOf mem a)
    (hfb : ∀ a ∈ G.chains.flatten, fbOf mem' (e a) = fbOf mem a) :
    MdbInv mem' ⟨G.chains.map (List.map e), Mdb.conjPar e G.par⟩ := by
  have hmem : ∀ z, z ∈ (G.chains.map (List.map e)).flatten ↔ e.symm z ∈ G.chains.flatten := by
    intro z
    simp only [List.map_flatten.symm, List.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩; simpa using ha
    · intro h; exact ⟨_, h, by simp⟩
  have hD : ∀ y x, Mdb.Desc (Mdb.conjPar e G.par) y x ↔ Mdb.Desc G.par (e.symm y) (e.symm x) := by
    intro y x
    have := Mdb.desc_conj e G.par (e.symm y) (e.symm x)
    simpa using this
  have hpm : ∀ x y, x ∈ G.chains.flatten → y ∈ G.chains.flatten → isPM mem' (e x) (e y) = isPM mem x y := by
    intro x y hx hy
    unfold isPM
    rw [hrev x hx, hfb y hy]
    exact isPF_congr (hcap x hx).1 (hcap x hx).2 (hcap y hy).1 (hcap y hy).2
  have hsm : ∀ x y, x ∈ G.chains.flatten → y ∈ G.chains.flatten → srM mem' (e x) (e y) = srM mem x y := by
    intro x y hx hy; unfold srM; exact srB_congr (hcap x hx).1 (hcap y hy).1
  have hnx : ∀ y ∈ G.chains.flatten, nextOf mem y ≠ 0#u64 → nextOf mem y ∈ G.chains.flatten := by
    intro y hy hn
    rcases hM.next_mem hy with h | h
    · exact absurd h hn
    · exact h.1
  have hn0 : ∀ y ∈ G.chains.flatten, nextOf mem' (e y) ≠ 0#u64 → nextOf mem y ≠ 0#u64 := by
    intro y hy h h0; rw [hnext y hy, h0, he0] at h; exact h rfl
  refine ⟨fun c p h => ?_, fun x y h => ?_, fun y hy hn x hx hd => ?_, fun ch hch => ?_,
    fun y hy hn hb hs hbd hb0 => ?_, fun x hx hu => ?_, fun x hx hz => ?_⟩
  · change (G.par (e.symm c)).map e = some p at h
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [hrev q (hM.tree.par_mem _ _ hq).2]; exact hI.orig _ _ hq
  · have h' := (hD y x).1 h
    obtain ⟨h1, h2⟩ := desc_mem hM h'
    have := hpm _ _ h2 h1
    simp only [Equiv.apply_symm_apply] at this
    rw [this]; exact hI.desc _ _ h'
  · have hy' := (hmem y).1 hy
    obtain ⟨y0, rfl⟩ : ∃ y0, y = e y0 := ⟨e.symm y, by simp⟩
    simp only [Equiv.symm_apply_apply] at hy'
    have hn' := hn0 y0 hy' hn
    rw [hnext y0 hy'] at hd ⊢
    obtain ⟨x0, rfl⟩ : ∃ x0, x = e x0 := ⟨e.symm x, by simp⟩
    have hx' : x0 = y0 ∨ Mdb.Desc G.par y0 x0 := by
      rcases hx with h | h
      · exact Or.inl (e.injective h)
      · exact Or.inr (by simpa using (hD _ _).1 h)
    have hd' : ¬ Mdb.Desc G.par (nextOf mem y0) x0 := fun h => hd (by rw [hD]; simpa using h)
    have hxm : x0 ∈ G.chains.flatten := by
      rcases hx' with h | h
      · rw [h]; exact hy'
      · exact (desc_mem hM h).2
    rw [hpm _ _ hxm (hnx y0 hy' hn')]
    exact hI.after y0 hy' hn' x0 hx' hd'
  · obtain ⟨ch0, hch0, rfl⟩ := List.mem_map.1 hch
    exact Mdb.chunkL_map e (hI.chunk _ hch0) (fun u hu v hv =>
      srF_congr (hsm u v (List.mem_flatten.2 ⟨_, hch0, hu⟩) (List.mem_flatten.2 ⟨_, hch0, hv⟩))
        (isFrame_of_shape (hcap u (List.mem_flatten.2 ⟨_, hch0, hu⟩)).1) (hrev u (List.mem_flatten.2 ⟨_, hch0, hu⟩)))
  · have hy' := (hmem y).1 hy
    obtain ⟨y0, rfl⟩ : ∃ y0, y = e y0 := ⟨e.symm y, by simp⟩
    simp only [Equiv.symm_apply_apply] at hy'
    have hn' := hn0 y0 hy' hn
    have hw := hnx y0 hy' hn'
    rw [hnext y0 hy'] at hs hbd hb0 ⊢
    rw [hfb _ hw]
    rw [(hcap y0 hy').2, (hcap _ hw).2] at hbd
    rw [(hcap _ hw).2] at hb0
    rw [isBadged_of_shape (hcap y0 hy').1] at hb
    rw [hsm _ _ hy' hw] at hs
    exact hI.badges y0 hy' hn' hb hs hbd hb0
  · have hx' := (hmem x).1 hx
    obtain ⟨x0, rfl⟩ : ∃ x0, x = e x0 := ⟨e.symm x, by simp⟩
    simp only [Equiv.symm_apply_apply] at hx'
    rw [isUt_of_shape (hcap x0 hx').1] at hu
    rw [hrev x0 hx']; exact hI.utrev x0 hx' hu
  · have hx' := (hmem x).1 hx
    obtain ⟨x0, rfl⟩ : ∃ x0, x = e x0 := ⟨e.symm x, by simp⟩
    simp only [Equiv.symm_apply_apply] at hx'
    rw [isZb_of_shape (hcap x0 hx').1] at hz
    rw [hsm _ _ hx' hx']; exact hI.self x0 hx' hz

end

end Fl4Proofs.P3
