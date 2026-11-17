/-
P3 (DESIGN.md §9), scheduler: **the entry tail on `JAt`** (`jat_schedule`):
`JAtZ` mid-entry (the current thread's `CurInv` only unless a reschedule is
pending, the current SC's owner `CurOwn`) before FL4's `schedule` ⇒ `JAtZ`
and `CurInv` after.

* `JAtZ.schedPreW`: `schedule`'s mid-entry precondition (`SchedPreW`) from
  `JAtZ` and the domain scope.
* `FireHypW`: the TCB timers' hypothesis keeping `SchedPreW`.
* `jat_schedule`: `schedule_refinesW` gives `Inv`, `CurInv` and `ActIdle`
  after; named premise `hSchedRest` (as the SC steps' `ScStepP1`): the rest of `JAtZ`
  at `schedule`'s post, given those (`schedule`'s frame: the timers,
  `awaken`, `choose_thread`, `switch_sched_context`, the arch switch).
-/
import Fl4Proofs.P3.ScScheduleTop
import Fl4Proofs.P3.JointAt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **`schedule`'s mid-entry precondition from `JAtZ`** and the domain scope. -/
theorem JAtZ.schedPreW {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hd : σ.domainTime ≠ 0) : SchedPreW Z.T Z.C σ :=
  ⟨J.inv, J.cur, J.off, J.act, hd, J.own⟩

/-- The hypothesis on FL4's TCB timers keeping `SchedPreW` (`FireHyp` from a
mid-entry state). -/
def FireHypW (st : machine.Store S) [L : P1.LawfulStore st] (ar : machine.Arch A) (N T C : Set U64) (c : U64) :
    Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), SchedRel st N T C c s σ → NtfnStateRel N T (L.mem s) σ →
    NSC N C σ → SchedPreW T C σ → timer.fire st ar s a ⦃ r => ∃ σ1, Fires σ σ1 ∧ SchedRel st N T C c r.1 σ1 ∧
      NtfnStateRel N T (L.mem r.1) σ1 ∧ NSC N C σ1 ∧ SchedPreW T C σ1 ⦄

/-- **The entry tail on `JAt`** (module docstring). -/
theorem jat_schedule {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hd : σ.domainTime ≠ 0) (hnd : Fl4Spec.numDomains = 1)
    (hfire : FireHypW st arI Z.N Z.T Z.C Z.c) (hA : ArchSw st arI Z.N Z.T Z.C Z.c)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hSchedRest : sched.schedule st arI s a ⦃ r => ∀ σ1 σ', Fires σ σ1 →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → NtfnStateRel Z.N Z.T (L.mem r.1) σ' → NSC Z.N Z.C σ' → Inv σ' →
      CurInv σ' → ActIdle σ' →
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.1 r.2 σ' ⦄) :
    sched.schedule st arI s a ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.1 r.2 σ' ∧ CurInv σ' ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  refine WP.spec_mono (WP.spec_and (schedule_refinesW s a σ hS hR J.nsc hnd
    (hfire s a σ hS hR J.nsc (J.schedPreW hd)) hA hsni hsend hT) hSchedRest) ?_
  rintro r ⟨⟨σ1, σ', hF, hsc, hS', hR', hN', hI', hC', hA'⟩, hRest⟩
  obtain ⟨Ac', Lst', D', J'⟩ := hRest σ1 σ' hF hsc hS' hR' hN' hI' hC' hA'
  exact ⟨σ', Ac', Lst', D', J', hC'⟩

end

end

end Fl4Proofs.P3
