/-
P3 (DESIGN.md §9), CSpace: the derivation-tree relation after removing a
slot from its chain (what `empty_slot` does to the links).
-/
import Fl4Proofs.P3.MdbRename
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- How the slot words change when `x` is unlinked. -/
structure RemLinks (th : TypedHeap) (mem mem' : U64 → U64) (x : U64) : Prop where
  prev : ∀ a, IsSlot th a → prevOf mem' a = if a = x then 0#u64
    else if nextOf mem x ≠ 0#u64 ∧ a = nextOf mem x then prevOf mem x else prevOf mem a
  next : ∀ a, IsSlot th a → nextOf mem' a = if a = x then 0#u64
    else if prevOf mem x ≠ 0#u64 ∧ a = prevOf mem x then nextOf mem x else nextOf mem a
  cap_x : capAt mem' x = ok .Null
  cap_other : ∀ a, IsSlot th a → a ≠ x → capAt mem' a = capAt mem a

theorem MdbLinks.remove {th : TypedHeap} (hP : Placed th) {mem mem' : U64 → U64} {G : MdbGhost}
    (hM : MdbLinks th mem G) {x : U64} (hx : x ∈ G.chains.flatten) (hL : RemLinks th mem mem' x) :
    MdbLinks th mem' ⟨Mdb.removeChains x G.chains, Mdb.removePar x G.par⟩ := by
  have hslot : ∀ a, a ∈ G.chains.flatten → IsSlot th a := fun a h => ((hM.members a).1 h).1
  have hz : ∀ a, a ∈ G.chains.flatten → a ≠ 0#u64 := fun a h => (hslot a h).ne_zero hP
  have hnd := hM.tree.nodup
  obtain ⟨ch0, hch0, hxch⟩ := List.mem_flatten.1 hx
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hxch
  have hnd0 : (A ++ x :: B).Nodup := (List.nodup_flatten.1 hnd).1 _ hch0
  obtain ⟨hxA, hxB⟩ := Mdb.nodup_mid hnd0
  have hdisjAB : ∀ y, y ∈ A → y ∉ B := fun y hy hb =>
    (List.disjoint_of_nodup_append hnd0 hy (List.mem_cons_of_mem _ hb)).elim
  have hmem0 : ∀ y, y ∈ A ++ x :: B → y ∈ G.chains.flatten := fun y hy => List.mem_flatten.2 ⟨_, hch0, hy⟩
  have hc0 := hM.chain _ hch0
  -- `prev`/`next` of `x` are the neighbours in its chain
  have hN : (B = [] ∧ nextOf mem x = 0#u64) ∨ (∃ b0 B', B = b0 :: B' ∧ nextOf mem x = b0) := by
    cases B with
    | nil => left; exact ⟨rfl, by simpa using hM.last _ hch0 (by simp)⟩
    | cons b0 B' =>
      right; refine ⟨b0, B', rfl, ?_⟩
      rw [List.isChain_append] at hc0
      exact (List.isChain_cons_cons.1 hc0.2.1).1.1
  have hPv : (A = [] ∧ prevOf mem x = 0#u64) ∨ (∃ A' p, A = A' ++ [p] ∧ prevOf mem x = p) := by
    rcases List.eq_nil_or_concat A with rfl | ⟨A', p, rfl⟩
    · left; exact ⟨rfl, by simpa using hM.head _ hch0 (by simp)⟩
    · right; refine ⟨A', p, by simp, ?_⟩
      have hc := hc0
      simp only [List.concat_eq_append, List.append_assoc, List.singleton_append] at hc
      rw [List.isChain_append_cons_cons] at hc
      exact hc.2.1.2
  have hnotN : ∀ b, b ∉ B → ¬ (nextOf mem x ≠ 0#u64 ∧ b = nextOf mem x) := by
    rintro b hb ⟨h0, rfl⟩
    rcases hN with ⟨-, h⟩ | ⟨b0, B', rfl, h⟩
    · exact h0 h
    · exact hb (h ▸ List.mem_cons_self)
  have hnotP : ∀ a, a ∉ A → ¬ (prevOf mem x ≠ 0#u64 ∧ a = prevOf mem x) := by
    rintro a ha ⟨h0, rfl⟩
    rcases hPv with ⟨-, h⟩ | ⟨A', p, rfl, h⟩
    · exact h0 h
    · exact ha (h ▸ by simp)
  have hother : ∀ c, c ∈ G.chains → ∀ y, y ∈ c → c ≠ A ++ x :: B → y ∉ A ++ x :: B := by
    intro c hc y hy hne hy0
    exact hne (chain_unique hnd hc hch0 hy hy0)
  set R := fun a b => nextOf mem a = b ∧ prevOf mem b = a
  set R' := fun a b => nextOf mem' a = b ∧ prevOf mem' b = a
  have hkeep : ∀ a b, a ∈ G.chains.flatten → b ∈ G.chains.flatten → a ≠ x → b ≠ x →
      ¬ (prevOf mem x ≠ 0#u64 ∧ a = prevOf mem x) → ¬ (nextOf mem x ≠ 0#u64 ∧ b = nextOf mem x) →
      R a b → R' a b := by
    rintro a b ha hb hax hbx haP hbN ⟨h1, h2⟩
    exact ⟨by rw [hL.next a (hslot a ha), if_neg hax, if_neg haP, h1],
      by rw [hL.prev b (hslot b hb), if_neg hbx, if_neg hbN, h2]⟩
  have hmemR : ∀ y, y ∈ (Mdb.removeChains x G.chains).flatten ↔ y ∈ G.chains.flatten ∧ y ≠ x :=
    fun y => Mdb.mem_removeChains hnd
  refine ⟨Mdb.MdbOK.remove hM.tree hM.no_self_par, ?_, ?_, ?_, ?_, ?_⟩
  · intro ch' hch'
    unfold Mdb.removeChains at hch'
    have := (List.mem_filter.1 hch').2
    simpa using this
  · -- links
    intro ch' hch'
    unfold Mdb.removeChains at hch'
    obtain ⟨hch', -⟩ := List.mem_filter.1 hch'
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
    by_cases hxc : x ∈ ch
    · have e := chain_unique hnd hch hch0 hxc hxch
      subst e
      rw [Mdb.erase_mid hxA]
      have hc := hc0
      rw [List.isChain_append] at hc ⊢
      obtain ⟨hcA, hcB, hlink⟩ := hc
      have hcB' := (List.isChain_cons.1 hcB).2
      refine ⟨?_, ?_, ?_⟩
      · apply hcA.imp_of_mem_imp
        intro a b ha hb hr
        refine hkeep a b (hmem0 a (by simp [ha])) (hmem0 b (by simp [hb])) (fun e => hxA (e ▸ ha))
          (fun e => hxA (e ▸ hb)) ?_ (hnotN b (hdisjAB b hb)) hr
        rintro ⟨h0, rfl⟩
        have := (hM.prev_link hx h0).2
        rw [hr.1] at this
        exact hxA (this ▸ hb)
      · apply hcB'.imp_of_mem_tail_imp
        intro a b ha hb hr
        have hbB : b ∈ B := List.mem_of_mem_tail hb
        refine hkeep a b (hmem0 a (by simp [ha])) (hmem0 b (by simp [hbB])) (fun e => hxB (e ▸ ha))
          (fun e => hxB (e ▸ hbB)) (hnotP a (fun h => hdisjAB a h ha)) ?_ hr
        rintro ⟨h0, rfl⟩
        rcases hN with ⟨rfl, -⟩ | ⟨b0, B', rfl, hb0⟩
        · simp at ha
        · have hn' : (b0 :: B').Nodup :=
            (List.nodup_append.1 (List.nodup_cons.1 (List.nodup_middle.1 hnd0)).2).2.1
          simp only [List.tail_cons] at hb
          rw [hb0] at hb
          exact (List.nodup_cons.1 hn').1 hb
      · intro p hp b0 hb0
        rcases hPv with ⟨rfl, -⟩ | ⟨A', p', rfl, hp'⟩
        · simp at hp
        · have hpp : p = p' := by simpa using hp.symm
          rw [← hpp] at hp'
          rcases hN with ⟨rfl, -⟩ | ⟨b1, B', rfl, hb1⟩
          · simp at hb0
          · have hbb : b0 = b1 := by simpa using hb0.symm
            rw [← hbb] at hb1
            have hpm : p ∈ G.chains.flatten := hmem0 p (by simp [hpp])
            have hbm : b0 ∈ G.chains.flatten := hmem0 b0 (by simp [hbb])
            have hp0 : prevOf mem x ≠ 0#u64 := by rw [hp']; exact hz _ hpm
            have hn0 : nextOf mem x ≠ 0#u64 := by rw [hb1]; exact hz _ hbm
            refine ⟨?_, ?_⟩
            · rw [hL.next p (hslot p hpm), if_neg (fun e => hxA (by rw [← e, hpp]; simp)),
                if_pos ⟨hp0, hp'.symm⟩, hb1]
            · rw [hL.prev b0 (hslot b0 hbm), if_neg (fun e => hxB (by rw [← e, hbb]; simp)),
                if_pos ⟨hn0, hb1.symm⟩, hp']
    · rw [Mdb.erase_not_mem' hxc]
      apply (hM.chain ch hch).imp_of_mem_imp
      intro a b ha hb hr
      have hne : ch ≠ A ++ x :: B := fun e => hxc (e ▸ hxch)
      have ha0 := hother ch hch a ha hne
      have hb0 := hother ch hch b hb hne
      exact hkeep a b (List.mem_flatten.2 ⟨_, hch, ha⟩) (List.mem_flatten.2 ⟨_, hch, hb⟩)
        (fun e => hxc (e ▸ ha)) (fun e => hxc (e ▸ hb))
        (hnotP a (fun h => ha0 (by simp [h]))) (hnotN b (fun h => hb0 (by simp [h]))) hr
  · -- heads
    intro ch' hch' hne'
    unfold Mdb.removeChains at hch'
    obtain ⟨hch', -⟩ := List.mem_filter.1 hch'
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
    by_cases hxc : x ∈ ch
    · have e := chain_unique hnd hch hch0 hxc hxch
      subst e
      simp only [Mdb.erase_mid hxA] at hne' ⊢
      cases A with
      | cons a0 A'' =>
        have h0 := hM.head _ hch0 (by simp)
        simp only [List.cons_append, List.head_cons] at h0 ⊢
        have ha0 : a0 ∈ G.chains.flatten := hmem0 a0 (by simp)
        rw [hL.prev a0 (hslot a0 ha0), if_neg (fun e => hxA (by simp [e])),
          if_neg (hnotN a0 (hdisjAB a0 (by simp))), h0]
      | nil =>
        simp only [List.nil_append] at hne' ⊢
        rcases hN with ⟨rfl, -⟩ | ⟨b0, B', rfl, hb0⟩
        · exact absurd rfl hne'
        · simp only [List.head_cons]
          have hbm : b0 ∈ G.chains.flatten := hmem0 b0 (by simp)
          have hn0 : nextOf mem x ≠ 0#u64 := by rw [hb0]; exact hz _ hbm
          rcases hPv with ⟨-, hp0⟩ | ⟨A', p', h, -⟩
          · rw [hL.prev b0 (hslot b0 hbm), if_neg (fun e => hxB (by simp [e])), if_pos ⟨hn0, hb0.symm⟩, hp0]
          · simp at h
    · simp only [Mdb.erase_not_mem' hxc] at hne' ⊢
      have hh : ch.head hne' ∈ ch := List.head_mem hne'
      have hne : ch ≠ A ++ x :: B := fun e => hxc (e ▸ hxch)
      have hh0 := hother ch hch _ hh hne
      have hhx : ch.head hne' ≠ x := fun e => hxc (e ▸ hh)
      rw [hL.prev _ (hslot _ (List.mem_flatten.2 ⟨_, hch, hh⟩)), if_neg hhx,
        if_neg (hnotN _ (fun h => hh0 (by simp [h]))), hM.head ch hch hne']
  · -- lasts
    intro ch' hch' hne'
    unfold Mdb.removeChains at hch'
    obtain ⟨hch', -⟩ := List.mem_filter.1 hch'
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
    by_cases hxc : x ∈ ch
    · have e := chain_unique hnd hch hch0 hxc hxch
      subst e
      simp only [Mdb.erase_mid hxA] at hne' ⊢
      rcases hN with ⟨rfl, hn0⟩ | ⟨b0, B', rfl, hb0⟩
      · simp only [List.append_nil] at hne' ⊢
        rcases hPv with ⟨rfl, -⟩ | ⟨A', p, rfl, hp⟩
        · exact absurd rfl hne'
        · simp only [List.getLast_append_singleton]
          have hpm : p ∈ G.chains.flatten := hmem0 p (by simp)
          have hp0 : prevOf mem x ≠ 0#u64 := by rw [hp]; exact hz _ hpm
          rw [hL.next p (hslot p hpm), if_neg (fun e => hxA (by simp [e])), if_pos ⟨hp0, hp.symm⟩, hn0]
      · have h0 := hM.last _ hch0 (by simp)
        have e1 : (A ++ b0 :: B').getLast hne' = (b0 :: B').getLast (by simp) := by
          rw [List.getLast_append_of_ne_nil _ (by simp)]
        have e2 : (A ++ x :: b0 :: B').getLast (by simp) = (b0 :: B').getLast (by simp) := by
          rw [List.getLast_append_of_ne_nil _ (by simp)]; simp [List.getLast_cons]
        rw [e2] at h0; rw [e1]
        have hl : (b0 :: B').getLast (by simp) ∈ b0 :: B' := List.getLast_mem _
        have hlm : (b0 :: B').getLast (by simp) ∈ G.chains.flatten := hmem0 _ (by simp [hl])
        have hlx : (b0 :: B').getLast (by simp) ≠ x := fun e => hxB (e ▸ hl)
        rw [hL.next _ (hslot _ hlm), if_neg hlx,
          if_neg (hnotP _ (fun h => hdisjAB _ h hl)), h0]
    · simp only [Mdb.erase_not_mem' hxc] at hne' ⊢
      have hh : ch.getLast hne' ∈ ch := List.getLast_mem hne'
      have hne : ch ≠ A ++ x :: B := fun e => hxc (e ▸ hxch)
      have hh0 := hother ch hch _ hh hne
      have hhx : ch.getLast hne' ≠ x := fun e => hxc (e ▸ hh)
      rw [hL.next _ (hslot _ (List.mem_flatten.2 ⟨_, hch, hh⟩)), if_neg hhx,
        if_neg (hnotP _ (fun h => hh0 (by simp [h]))), hM.last ch hch hne']
  · intro a
    rw [hmemR, hM.members a]
    by_cases hax : a = x
    · subst hax
      simp only [ne_eq, not_true_eq_false, and_false, false_iff, not_and, not_exists]
      intro _ c hc; rw [hL.cap_x] at hc
      have : capability.Cap.Null = c := by simpa using hc
      exact fun h => h this.symm
    · constructor
      · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨h1, by rw [hL.cap_other a h1 hax]; exact h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by rw [← hL.cap_other a h1 hax]; exact h2⟩, hax⟩

/-- The spec's CDT after `empty_slot`: the slot's children get its parent. -/
theorem CdtRel.remove {Z : Type} {th : TypedHeap} (hP : Placed th) {mem mem' : U64 → U64}
    {σ σ' : Fl4Spec.State Z} {G : MdbGhost} (hC : CdtRel th mem σ G) (chains' : List (List U64))
    {xs : Fl4Spec.CslotPtr} (hxs : AbsSlot th xs)
    (hcdt : σ'.cdt = Function.update (fun p => if σ.cdt p = some xs then σ.cdt xs else σ.cdt p) xs none)
    (hio : σ'.isOriginalCap = Function.update σ.isOriginalCap xs false)
    (hrev : ∀ a, IsSlot th a → revOf mem' a = if a = cslotAddr xs then false else revOf mem a) :
    CdtRel th mem' σ' ⟨chains', Mdb.removePar (cslotAddr xs) G.par⟩ := by
  have hiff : ∀ sl, AbsSlot th sl → (σ.cdt sl = some xs ↔ G.par (cslotAddr sl) = some (cslotAddr xs)) := by
    intro sl hsl
    rw [← hC.cdt sl hsl]
    constructor
    · intro h; rw [h]; rfl
    · intro h
      obtain ⟨q, hq, hqa⟩ := Option.map_eq_some_iff.1 h
      rw [hq, cslotAddr_inj hP (hC.cdt_slot sl q hq).2 hxs hqa]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro sl hsl
    show Option.map cslotAddr (σ'.cdt sl) = Mdb.removePar _ G.par (cslotAddr sl)
    rw [hcdt]
    by_cases h1 : sl = xs
    · rw [h1]; simp [Mdb.removePar]
    · have hne : cslotAddr sl ≠ cslotAddr xs := fun e => h1 (cslotAddr_inj hP hsl hxs e)
      simp only [Function.update_of_ne h1, Mdb.removePar, hne, ↓reduceIte]
      by_cases h2 : σ.cdt sl = some xs
      · rw [if_pos h2, if_pos ((hiff sl hsl).1 h2), hC.cdt xs hxs]
      · rw [if_neg h2, if_neg (fun h => h2 ((hiff sl hsl).2 h)), hC.cdt sl hsl]
  · intro sl q hq
    rw [hcdt] at hq
    by_cases h1 : sl = xs
    · rw [h1] at hq; simp at hq
    · rw [Function.update_of_ne h1] at hq
      by_cases h2 : σ.cdt sl = some xs
      · rw [if_pos h2] at hq
        exact ⟨(hC.cdt_slot _ _ h2).1, (hC.cdt_slot _ _ hq).2⟩
      · rw [if_neg h2] at hq; exact hC.cdt_slot _ _ hq
  · intro sl hsl
    rw [hio, hrev _ hsl.isSlot]
    by_cases h1 : sl = xs
    · rw [h1]; simp
    · have hne : cslotAddr sl ≠ cslotAddr xs := fun e => h1 (cslotAddr_inj hP hsl hxs e)
      rw [Function.update_of_ne h1, if_neg hne]; exact hC.orig sl hsl
  · intro a b hab
    change Mdb.removePar _ G.par a = some b at hab
    unfold Mdb.removePar at hab
    by_cases hax : a = cslotAddr xs
    · simp [hax] at hab
    · rw [if_neg hax] at hab
      by_cases hp : G.par a = some (cslotAddr xs)
      · exact hC.par_slot a _ hp
      · rw [if_neg hp] at hab; exact hC.par_slot a b hab

end

end Fl4Proofs.P3
