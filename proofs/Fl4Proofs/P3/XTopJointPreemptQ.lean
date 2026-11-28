/-
P3 (DESIGN.md §9): **the current thread in no ready queue at a preemption
hole, proved** (KENTRY-PLAN kp16): kp15's [J] premise `JHoleCtNQHyp` (l4v
`ct_not_queued` at a hole) removed.

* ScPPR's `PPR0` carries `CtNQ` (the current thread in no ready queue) from
  the invocation's start (`JAtZ.ppr0_start` from JEntryAt's `ctnq`) through
  the deletion and reset loops: `PPK.nq` for the CNode/kernel-state/restart/
  TCB-field/scheduler steps, SpecPPRQ's `ctnq_finaliseCap` for the
  finalisations (their enqueues are the restarts of threads queued on the
  finalised endpoint or notification, blocked there, so not the current
  thread, `CtOK`). `JAtPre` holds `PPR0` at the preemption point's base;
  the preemption point keeps the queues: `jAtPre_holeQ`.
* `JPreemptRestHypEQ` [W] := XTopJointPreemptE's `JPreemptRestHypE` with an
  extra `CtNQ σ →` (narrower); `jPreemptRestHypEQ_ofC` proves it from
  XTopJointPreemptA's `JPreemptRestHypC` [W] alone (kp15's
  `jPreemptRestHypE_ofC` without `JHoleCtNQHyp`); `hPre_ofZQ`,
  `dispatch_invokeJPZA`, `dispatch_invokeJEPZA` (NEW TOP: premises as
  dispatch_invokeJEPZE with `hRC : JPreemptRestHypC` for `hRest`).
-/
import Fl4Proofs.P3.ScChargeTA
import Fl4Proofs.P3.XTopJointPreemptE
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

variable (arI) in
/-- **The preemption path outside `PPCov ∨ PPCovT ∨ PPCovI` at a hole with
the current thread in no ready queue** [W] (kp16: XTopJointPreemptE's
`JPreemptRestHypE` with `CtNQ σ`, narrower). Proved from
`JPreemptRestHypC` [W] (`jPreemptRestHypEQ_ofC`). -/
def JPreemptRestHypEQ (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAtV (L := L) arI AR s a σ → NativeScope σ →
    σ.curThread ≠ σ.idleThread → Vs.NoSwitch σ → CurScFree σ → CtOK σ → Chg σ → CtNQ σ →
    CurInv σ → Fl4Spec.schedulable σ.curThread σ = true →
    ¬ (∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
      Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true) →
    ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) →
    syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ (r.2.1, r.2.2) ⦄

theorem jPreemptRestHypEQ_of (h : JPreemptRestHypE (L := L) arI AR) : JPreemptRestHypEQ (L := L) arI AR :=
  fun s a σ hJ hn hi hs hf hc hg _ => h s a σ hJ hn hi hs hf hc hg

end

end

end Fl4Proofs.P3
