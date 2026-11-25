/-
# P2 (line stpost, generation 7): the accepted timer interrupt keeps the chain's stable ghosts

SlJStPostTm's `jreachSt_tmSt` for the local timer interrupt `handle_timer_irq_local … w p`
(fl4-sync's `local_timer_irq`).

* `LocIrq`: the accepted timer-interrupt runs (any line `w`, entry Arch value `a1`, plan `p`) with their
  spec outcomes (`EvOut false .interrupt`). The hardware fact `IrqHw` is an input of the step lemma, not
  part of the relation (the relation is only read through `LocSt`'s stable-ghost conjuncts).
* **`jreachSt_irqSt`**: from every `JReachSt` state, an accepted `handle_timer_irq_local … w p` (taken
  at `a1` with `IrqHw AR MR a a1 σ w`) has an `EvOut false .interrupt` outcome `σ'` with `JReachSt` at
  `(s', a', σ')` through a `LocSt` step: P3's `kernel_entry_irq_localSt17` (StPostIrqTop) at the
  chain's own ghosts; the kernel-state base by `ksbEq_of_irqNode` with `evOut_irqNode`.

Inputs: U29's interrupt-clause inputs (`hI : IrqHw` [P], `hFin : KFinEv13`); platform premises a
subset of U29's. No new premise. So `LocKeepSt (LocSt LocIrq …)` holds by `locKeepSt_st`.
-/
import Fl4Proofs.P2.SlJStPostTm
import Fl4Proofs.P3.StPostIrqTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- (stpost) **The accepted timer-interrupt runs** with their spec outcomes (module docstring). -/
def LocIrq (s : S) (_a : A) (σ : Fl4Spec.State Unit) (s' : S) (a' : A) (σ' : Fl4Spec.State Unit) : Prop :=
  ∃ (w : U64) (a1 : A) (p : localtimer.TimerIrqPlan),
    localtimer.handle_timer_irq_local st arI s a1 w p = ok (true, s', a') ∧
    Fl4Proofs.P3.EvOut false .interrupt σ σ'

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- (stpost) **The accepted timer interrupt from a `JReachSt` state** (module docstring). -/
theorem jreachSt_irqSt [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR)
    {Loc : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop}
    {th : TypedHeap} {B : Set (U64 × Fl4Spec.Word)} {H : Heap} {Cs : Set U64} {k : U64}
    (hK : LocKeepSt (L := L) arI AR Loc th B H Cs)
    (hsub : ∀ s a σ s' a' σ', LocSt (L := L) arI AR (LocIrq (st := st) arI) th B H Cs s a σ s' a' σ' →
      Loc s a σ s' a' σ')
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachSt (L := L) arI AR MR Loc th B H Cs k s a σ)
    (w : U64) (a1 : A) (p : localtimer.TimerIrqPlan) (hI : IrqHw AR MR a a1 σ w)
    (hFin : KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ)
    {s' : S} {a' : A} (hrun : localtimer.handle_timer_irq_local st arI s a1 w p = ok (true, s', a')) :
    ∃ σ', Fl4Proofs.P3.EvOut false .interrupt σ σ' ∧
      JReachSt (L := L) arI AR MR Loc th B H Cs k s' a' σ' := by
  obtain ⟨Z, Ac, Lst, D, hth, hB, -, J, hvx⟩ := hJ.atSt' hK
  have := hvx
  have hT' := kernel_entry_irq_localSt17 hARI hA hnd hM hKD hPA hIA hT hmax htu hRef hDR hJ.reach J w a1 p hI hFin
  rw [hrun, WP.spec_ok] at hT'
  obtain ⟨σ', hO, hR', G, V, Ac', Lst', D', J'⟩ := hT' rfl
  have hks : L.ksb s' = L.ksb s := ksbEq_of_irqNode J J' (evOut_irqNode hO)
  refine ⟨σ', hO, .loc hJ (hsub _ _ _ _ _ _ ⟨⟨w, a1, p, hrun, hO⟩, hks,
    Z.mv G V, Ac', Lst', D', hth, hB, J', ⟨hvx.eq⟩⟩) hR'⟩

end

end Fl4Proofs.P2.PathObl
