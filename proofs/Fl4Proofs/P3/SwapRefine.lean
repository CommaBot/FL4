/-
P3 (DESIGN.md §9), CSpace: **`cdt::swap` refines l4v `cap_swap`**
(nondeterministic spec, `Z = Unit`), for two distinct CNode slots of the
typed heap holding caps.

`swap_refines`: FL4's `swap c1 s1 c2 s2` ends in a state related to the
spec's single outcome of `cap_swap a1 s1 a2 s2`; the ghost tree is renamed
by the transposition of the two slots (`Mdb.conjPar`, `MdbLinks.rename`), as
the spec's `cdt` and `is_original_cap` are. Adjacent slots (one the other's
`next`) are covered: `swap_fields` computes every slot field after the
swap, including seL4's re-read of `slot2`'s links.
-/
import Fl4Proofs.P3.Swap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

theorem swap_cdt_eq {Z : Type} (σ : Fl4Spec.State Z) (s1 s2 : Fl4Spec.CslotPtr) (hne : s1 ≠ s2) :
    (let cdt' := fun n => if σ.cdt n = some s1 then some s2 else if σ.cdt n = some s2 then some s1 else σ.cdt n
     Function.update (Function.update cdt' s1 (cdt' s2)) s2 (cdt' s1)) =
      fun r => (σ.cdt (Equiv.swap s1 s2 r)).map (Equiv.swap s1 s2) := by
  have hc : ∀ n, (if σ.cdt n = some s1 then some s2 else if σ.cdt n = some s2 then some s1 else σ.cdt n) =
      (σ.cdt n).map (Equiv.swap s1 s2) := by
    intro n
    cases h : σ.cdt n with
    | none => simp
    | some q =>
      by_cases h1 : q = s1
      · subst h1; simp
      · by_cases h2 : q = s2
        · subst h2; simp [Ne.symm hne]
        · simp [h1, h2, Equiv.swap_apply_of_ne_of_ne h1 h2]
  funext r
  simp only [hc]
  by_cases h1 : r = s1
  · subst h1; simp [hne]
  · by_cases h2 : r = s2
    · subst h2; simp
    · simp [Function.update_of_ne h1, Function.update_of_ne h2, Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem swap_io_eq {Z : Type} (σ : Fl4Spec.State Z) (s1 s2 : Fl4Spec.CslotPtr) (hne : s1 ≠ s2) :
    Function.update (Function.update σ.isOriginalCap s1 (σ.isOriginalCap s2)) s2 (σ.isOriginalCap s1) =
      fun r => σ.isOriginalCap (Equiv.swap s1 s2 r) := by
  funext r
  by_cases h1 : r = s1
  · subst h1; simp [hne]
  · by_cases h2 : r = s2
    · subst h2; simp
    · simp [Function.update_of_ne h1, Function.update_of_ne h2, Equiv.swap_apply_of_ne_of_ne h1 h2]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem swap_refines (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    {p1 p2 : U64} {r1 r2 : Nat} (hp1 : th p1 = some (.cnode r1)) (hp2 : th p2 = some (.cnode r2))
    {i1 i2 : List Bool} (hl1 : i1.length = r1) (hl2 : i2.length = r2)
    (hne : (p1.bv, i1) ≠ (p2.bv, i2))
    {o1 o2 : capability.Cap} (ho1 : capAt (L.mem s) (cslotAddr (p1.bv, i1)) = ok o1) (hon1 : o1 ≠ .Null)
    (ho2 : capAt (L.mem s) (cslotAddr (p2.bv, i2)) = ok o2) (hon2 : o2 ≠ .Null)
    (c1 : capability.Cap) (a1 : Fl4Spec.Cap) (hca1 : CapRel c1 a1) (hcv1 : CapValid th c1) (he1 : EncWf c1)
    (hcn1 : c1 ≠ .Null)
    (c2 : capability.Cap) (a2 : Fl4Spec.Cap) (hca2 : CapRel c2 a2) (hcv2 : CapValid th c2) (he2 : EncWf c2)
    (hcn2 : c2 ≠ .Null) :
    cdt.swap st s c1 (cslotAddr (p1.bv, i1)) c2 (cslotAddr (p2.bv, i2)) ⦃ s' =>
      ∃ σ' G', Fl4Spec.capSwap (Z := Unit) a1 (p1.bv, i1) a2 (p2.bv, i2) σ = ({((), σ')}, False) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧ MdbLinks th (L.mem s') G' ∧
        CdtRel th (L.mem s') σ' G' ⦄ := by
  have hA1 : AbsSlot th (p1.bv, i1) := ⟨p1, rfl, Or.inl (by simpa [hl1] using hp1)⟩
  have hA2 : AbsSlot th (p2.bv, i2) := ⟨p2, rfl, Or.inl (by simpa [hl2] using hp2)⟩
  have hs1 := hA1.isSlot
  have hs2 := hA2.isSlot
  have hAne : cslotAddr (p1.bv, i1) ≠ cslotAddr (p2.bv, i2) := fun h => hne (cslotAddr_inj hP hA1 hA2 h)
  have hm1 : cslotAddr (p1.bv, i1) ∈ G.chains.flatten := (hM.members _).2 ⟨hs1, o1, ho1, hon1⟩
  have hm2 : cslotAddr (p2.bv, i2) ∈ G.chains.flatten := (hM.members _).2 ⟨hs2, o2, ho2, hon2⟩
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hNx : ∀ a, a ∈ G.chains.flatten → nextOf (L.mem s) a = 0#u64 ∨ IsSlot th (nextOf (L.mem s) a) := by
    intro a ha; rcases hM.next_mem ha with h | ⟨h, -⟩ <;> [exact Or.inl h; exact Or.inr (hslot _ h)]
  have hPx : ∀ a, a ∈ G.chains.flatten → prevOf (L.mem s) a = 0#u64 ∨ IsSlot th (prevOf (L.mem s) a) := by
    intro a ha; by_cases h : prevOf (L.mem s) a = 0#u64
    · exact Or.inl h
    · exact Or.inr (hslot _ (hM.prev_link ha h).1)
  obtain ⟨cs1, hk1, hwf1, -⟩ := hR.cnode p1 r1 hp1
  apply WP.spec_mono (swap_fields hP s c1 c2 _ _ hs1 hs2 hAne he1 he2 (hPx _ hm1) (hNx _ hm1)
    (hPx _ hm2) (hNx _ hm2))
  intro s' hW
  have hEq1 : cslotAddr (p1.bv, i1) = slotOf p1 (blVal 0 i1) := slotAddr_ofBl p1 i1
  have hEq2 : cslotAddr (p2.bv, i2) = slotOf p2 (blVal 0 i2) := slotAddr_ofBl p2 i2
  have hcap1 : ∀ x, IsSlot th x → capAt (L.mem (wrCap (L := L) s (cslotAddr (p1.bv, i1)) c2)) x =
      if x = slotOf p1 (blVal 0 i1) then ok c2 else capAt (L.mem s) x := by
    intro x hx; rw [capAt_wrCap hP s hs1 he2 hx, hEq1]
  obtain ⟨hR1, hV1⟩ := StateRel.update_cnode_slot hR hV hP hp1 hk1 hwf1 hl1 hca2 hcv2 hcap1
  have h1 := setCap_cnode (Z := Unit) a2 hk1 hwf1 hl1
  obtain ⟨cs2, hk2, hwf2, -⟩ := hR1.cnode p2 r2 hp2
  have hcap2 : ∀ x, IsSlot th x → capAt (L.mem s') x =
      if x = slotOf p2 (blVal 0 i2) then ok c1
      else capAt (L.mem (wrCap (L := L) s (cslotAddr (p1.bv, i1)) c2)) x := by
    intro x hx
    rw [(hW x hx).1, capAt_wrCap hP s hs1 he2 hx, ← hEq2]
  obtain ⟨hR2, hV2⟩ := StateRel.update_cnode_slot hR1 hV1 hP hp2 hk2 hwf2 hl2 hca1 hcv1 hcap2
  have h2 := setCap_cnode (Z := Unit) a1 hk2 hwf2 hl2
  have hsw := capSwap_eq h1 h2 (by simp [setCnodeSlot]) (by simp [setCnodeSlot])
  refine ⟨_, ⟨G.chains.map (List.map (Equiv.swap (cslotAddr (p1.bv, i1)) (cslotAddr (p2.bv, i2)))),
    Mdb.conjPar (Equiv.swap (cslotAddr (p1.bv, i1)) (cslotAddr (p2.bv, i2))) G.par⟩, hsw,
    StateRel.of_kheap hR2 rfl, hV2,
    MdbLinks.rename (e := Equiv.swap (cslotAddr (p1.bv, i1)) (cslotAddr (p2.bv, i2))) hM ?_, ?_⟩
  · exact RenLinks.swap hP hM hm1 hm2 hAne hcn1 hcn2 (fun x hx => ⟨(hW x hx).1, (hW x hx).2.1, (hW x hx).2.2.1⟩)
  · refine CdtRel.swap hP hC _ hA1 hA2 hne ?_ ?_ ?_
    · exact swap_cdt_eq σ _ _ hne
    · exact swap_io_eq σ _ _ hne
    · intro x hx
      rw [(hW x hx).2.2.2]
      by_cases e2 : x = cslotAddr (p2.bv, i2)
      · rw [if_pos e2, e2, Equiv.swap_apply_right]
      · by_cases e1 : x = cslotAddr (p1.bv, i1)
        · rw [if_neg e2, if_pos e1, e1, Equiv.swap_apply_left]
        · rw [if_neg e2, if_neg e1, Equiv.swap_apply_of_ne_of_ne e1 e2]

end

end

end Fl4Proofs.P3
