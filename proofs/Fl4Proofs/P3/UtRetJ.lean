/-
P3 (DESIGN.md §9), untyped: **`JAtZ`'s CSpace fields after a retype**
(`JCs` at the sets of the retype's outcome, handoff/utj.md "Round 4").

* `DelInv.retype`: `DelInv` after a retype from `DelInv` before and the
  retype's `RetExp`: a zombie after is a kept non-untyped cap (the new caps
  are no zombies, untyped caps stay untyped), and the empty slots keep clear
  links (`RetExp.nclr`: the creation loop writes no link word of a slot it
  leaves empty; the new objects' slots are zero memory).
-/
import Fl4Proofs.P3.UtEpSets
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- **`DelInv` across a retype** (module docstring). `hZ`: the old zombies'
objects are kept in the typed heap after. -/
theorem DelInv.retype {th th' : TypedHeap} {m m' : U64 → U64} {G G' : MdbGhost} {A k w : Nat}
    {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64} (hD : DelInv th m)
    (hE : RetExp th th' m m' G G' A k w dslot cj xs) (hM : MdbLinks th m G) (hM' : MdbLinks th' m' G')
    (hcj : ∀ j, j < w → ∀ p zt n, cj j ≠ .Zombie p zt n)
    (hZ : ∀ p zt n, ZOK th p zt n → ZOK th' p zt n) : DelInv th' m' := by
  -- a zombie after is the same zombie before, in an old slot
  have back : ∀ y, IsSlot th' y → ∀ p zt n, capV m' y = .Zombie p zt n →
      IsSlot th y ∧ capV m y = .Zombie p zt n := by
    intro y hy p zt n hz
    have hm : y ∈ G'.chains.flatten := (hM'.members y).2 ⟨hy, _, capAt_capV _ _, by rw [hz]; simp⟩
    rcases hE.gmem y hm with hy0 | ⟨j, hj, rfl⟩
    · refine ⟨((hM.members y).1 hy0).1, ?_⟩
      cases hu : isUt (capV m y)
      · rw [← (hE.keep y hy0 hu).2]; exact hz
      · have := hE.utk y hy0 hu; rw [hz] at this; cases this
    · exact absurd ((hE.newc j hj).symm.trans hz) (hcj j hj p zt n)
  refine ⟨fun y hy p zt n hz => ?_, fun y y' hy hy' hne p zt n p' zt' n' hz hz' => ?_, hE.nclr hD.nc⟩
  · obtain ⟨h1, h2⟩ := back y hy p zt n hz
    exact hZ p zt n (hD.zwf y h1 p zt n h2)
  · obtain ⟨h1, h2⟩ := back y hy p zt n hz
    obtain ⟨h1', h2'⟩ := back y' hy' p' zt' n' hz'
    exact hD.zu y y' h1 h1' hne p zt n p' zt' n' h2 h2'

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`JCs` after a retype**: `DelInv` by `DelInv.retype`, the untyped
invariant, finality (for any ghost of the links, `FinM.of_links`) and
`SpecFree` after (`SpecFree.retype`) at the sets with the retype's typed
heap and ghost. -/
theorem JCs.retype {Z' : XSets} {s' : S} {σ' : Fl4Spec.State Unit} {th th' : TypedHeap} {m : U64 → U64}
    {G G' : MdbGhost} {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64}
    (hth : Z'.th = th') (hG : Z'.G = G') (hD : DelInv th m)
    (hE : RetExp th th' m (L.mem s') G G' A k w dslot cj xs) (hM : MdbLinks th m G) (hP' : Placed th')
    (hM' : MdbLinks th' (L.mem s') G') (hcj : ∀ j, j < w → ∀ p zt n, cj j ≠ .Zombie p zt n)
    (hZ : ∀ p zt n, ZOK th p zt n → ZOK th' p zt n) (hU' : UtInv (L.mem s') G') (hFM : FinM (L.mem s') G')
    (hSF : Sched.SpecFree (L.mem s') G' σ') : JCs (L := L) Z' s' σ' := by
  subst hth hG
  exact ⟨hD.retype hE hM hM' hcj hZ, hU', fun G2 h2 => FinM.of_links hP' hM' h2 hFM, hSF⟩

end

end

end Fl4Proofs.P3
