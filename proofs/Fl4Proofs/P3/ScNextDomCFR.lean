/-
P3 (DESIGN.md §9), scheduler (KENTRY-PLAN.md sch9 (1)): **`schedule` from
`CurInvR`** (XTopJointJAtZR): `SchedPreW0R` (ScNextDomC's `SchedPreW0` with
`cur : CurInvR`), `awaken_refinesW0R` (the spec's `awaken` never sets
`resumeCurThread`: `CurInv` after only where it was asked before), and
`schedule_refinesWP0FR` (ScNextDomCF's `schedule_refinesWP0F`, copied): the
resume branch takes `CurInv` from `CurInvR` at the resumed action; the
switch branch no longer reads the old current thread's `CurInv` (the new
current thread is the idle thread or schedulable at the switch state,
`newcur_of2F`, as in the choose branch). So a pending switch over a blocked
current thread (`SwBlk`) is covered.
-/
import Fl4Proofs.P3.ScNextDomC
import Fl4Proofs.P3.ScNextDomF
import Fl4Proofs.P3.XTopJointJAtZR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3

noncomputable section

section Spec
open Fl4Spec

/-- `SchedPreW0` with `cur : CurInvR` (module docstring). -/
def SchedPreW0R (T C : Set U64) (σ : State Unit) : Prop :=
  Inv σ ∧ CurInvR σ ∧ OffOK σ ∧ ActIdle σ ∧ CurOwnW T C σ

end Spec

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

theorem awaken_refinesW0R {A : Type} {ar : machine.Arch A} {N C : Set U64} {c : U64} (s : S) (a : A)
    (σ : Fl4Spec.State Unit) {Pf : S × A → Fl4Spec.State Unit → Prop}
    (hfire : timer.fire st ar s a ⦃ r => ∃ σ1, Fires σ σ1 ∧ SchedRel st N T C c r.1 σ1 ∧
      NtfnStateRel N T (L.mem r.1) σ1 ∧ NSC N C σ1 ∧ SchedPreW0R T C σ1 ∧ Pf r σ1 ⦄) :
    sched.awaken st ar s a ⦃ r => ∃ σ1 σ2, Fires σ σ1 ∧ Fl4Spec.awaken (Z := Unit) σ1 = ({((), σ2)}, False) ∧
      SchedRel st N T C c r.1 σ2 ∧ NtfnStateRel N T (L.mem r.1) σ2 ∧ NSC N C σ2 ∧ SchedPreW0R T C σ2 ∧ Calm σ1 σ2 ∧
      (σ1.schedulerAction = .chooseNewThread → σ2.schedulerAction = .chooseNewThread) ∧
      (σ1.schedulerAction ≠ .resumeCurThread → σ2.schedulerAction ≠ .resumeCurThread) ∧
      (∀ u ∈ σ2.releaseQueue, u ∈ σ1.releaseQueue) ∧
      ∃ rf : S × A, Pf rf σ1 ∧ r.2 = rf.2 ∧ WritesIn st rf.1 r.1 (SFoot st T c rf.1) ⦄ := by
  unfold sched.awaken
  refine WP.spec_bind hfire ?_
  rintro ⟨s1, a1⟩ ⟨σ1, hF, hS1, hR1, hN1, ⟨hI1, hC1, hO1, ⟨hA1, hId1⟩, hW1⟩, hPf⟩
  refine WP.spec_bind (awaken_loop_refines s1 σ1 hS1 hR1 hN1 hI1 hA1 _ (rel_len_lt hS1)) ?_
  rintro s2 ⟨σ2, h2, hS2, hR2, hN2, hI2, ⟨hA2, hcn2, hnr2⟩, hc2, hsub, hw2⟩
  rw [WP.spec_ok]
  refine ⟨σ1, σ2, hF, h2, hS2, hR2, hN2, ⟨hI2, ?_, hO1.calm hc2, ⟨hA2, hId1.sub hc2 hsub⟩,
    hW1.sub hc2 hsub⟩, hc2, hcn2, hnr2, hsub, (s1, a1), hPf, rfl, hw2⟩
  exact fun e => (hC1 (Classical.byContradiction fun h => hnr2 h e)).sub hc2 hsub

end

end

end Fl4Proofs.P3.Sched
