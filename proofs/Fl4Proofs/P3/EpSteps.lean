/-
P3 (DESIGN.md §9), endpoints: the combined-relation side of the bundled step
lemmas (`EpSteps`, EpStepsBase).

* `SRN N T SR := SR ∧ NtfnStateRel N T`: `SR` with the notification relation
  carried along (the instance is `CombHyps.steps`, EpStepsN);
* `CombTailHyps`: the scheduler tails, keeping the notification footprint
  and view too; `CombTailHyps.tailN` gives the tails for `SRN`, and
  `EpScHyps.srn` the SC hypotheses.
-/
import Fl4Proofs.P3.EpComb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Defs
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- `SR` together with the notification relation. -/
def SRN (N T : Set U64) (SR : S → Fl4Spec.State Unit → Prop) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  SR s σ ∧ NtfnStateRel N T (L.mem s) σ

/-- The tail post-condition, keeping the notification footprint and view. -/
def TailPostN (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (SR : S → Fl4Spec.State Unit → Prop)
    (s : S) (σ : Fl4Spec.State Unit) (m : Fl4Spec.SMonad Unit Unit) (s' : S) : Prop :=
  ¬ (m σ).2 ∧ ∃ σ', ((), σ') ∈ (m σ).1 ∧ FootEq T E R B (L.mem s) (L.mem s') ∧ KView σ σ' ∧
    Notif.FootEq N T (L.mem s) (L.mem s') ∧ Notif.KView σ σ' ∧ SR s' σ'

/-- The scheduler tails (`EpTailHyps`), keeping the notification footprint
and view too. -/
structure CombTailHyps (A : Type) (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word))
    (SR : S → Fl4Spec.State Unit → Prop) : Prop where
  wakeTail : ∀ s (a : A) σ (t : U64), EpStateRel T E R B (L.mem s) σ → SR s σ → t ∈ T →
    SVK.WakeOK σ t.bv → (do
      let s1 ← endpoint.unblock_sporadic st s t
      let s2 ← sched.possible_switch_to st s1 t
      ok (s2, a)) ⦃ r => r.2 = a ∧ TailPostN st N T E R B SR s σ (specWakeTailE t.bv) r.1 ⦄
  sporadicAssert : ∀ s σ (t : U64), EpStateRel T E R B (L.mem s) σ → SR s σ → t ∈ T →
    endpoint.unblock_sporadic st s t ⦃ s' => ∃ σ', specSporadicAssert t.bv σ = ({((), σ')}, False) ∧
      FootEq T E R B (L.mem s) (L.mem s') ∧ KView σ σ' ∧
      Notif.FootEq N T (L.mem s) (L.mem s') ∧ Notif.KView σ σ' ∧ SR s' σ' ⦄
  switchTo : ∀ s (a : A) σ (t : U64), EpStateRel T E R B (L.mem s) σ → SR s σ → t ∈ T →
    SVK.ActReadyW σ → (do
      let s1 ← sched.possible_switch_to st s t
      ok (s1, a)) ⦃ r => r.2 = a ∧ TailPostN st N T E R B SR s σ (Fl4Spec.possibleSwitchTo t.bv) r.1 ⦄

end Defs

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- The SC hypotheses for `SRN`. -/
theorem EpScHyps.srn (h : EpScHyps st T E R B SR) : EpScHyps st T E R B (SRN st N T SR) :=
  ⟨fun s σ t x hS hk ht => h.scRel s σ t x hS.1 hk ht, h.sporadicSc⟩

/-- The tails for `SRN`. -/
theorem CombTailHyps.tailN (h : CombTailHyps st A N T E R B SR) (hP : CPlaced N T E R B) :
    EpTailHyps st A T E R B (SRN st N T SR) :=
  ⟨fun s a σ t hR hS ht hW => WP.spec_mono (h.wakeTail s a σ t hR hS.1 ht hW) fun _ ⟨h1, h2, σ', h3, h4, h5, h6, h7, h8⟩ =>
      ⟨h1, h2, σ', h3, h4, h5, h8, hS.2.frame hP.n h6 h7⟩,
   fun s σ t hR hS ht => WP.spec_mono (h.sporadicAssert s σ t hR hS.1 ht) fun _ ⟨σ', h1, h2, h3, h4, h5, h6⟩ =>
      ⟨σ', h1, h2, h3, h6, hS.2.frame hP.n h4 h5⟩,
   fun s a σ t hR hS ht hW => WP.spec_mono (h.switchTo s a σ t hR hS.1 ht hW) fun _ ⟨h1, h2, σ', h3, h4, h5, h6, h7, h8⟩ =>
      ⟨h1, h2, σ', h3, h4, h5, h8, hS.2.frame hP.n h6 h7⟩⟩

end

end

end Fl4Proofs.P3.Endp
