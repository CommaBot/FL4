/-
P3 (DESIGN.md §9): **the preemption path's charge of an unschedulable
current thread with `CurInv`** (KENTRY-PLAN kp14, (2c) part): FL4's
`mcs_preemption_point` and the spec's `preemption_path` charge with
`can_timeout_fault = false` when the current thread is not schedulable, so
an endpoint timeout handler (¬`NoTmoSend`) does not matter there:
XTopJointPreempt's `JHole.mcsPPJ` asks `PPCov` (incl. `NoTmoSend`) only for
the schedulable branch.

* `JHole.mcsPPJC`: that branch with `CurInv`, a non-idle current thread and
  no switch pending (ScChargeH's `JHole.chargeBudgetJ`), `JAt` after.
* `JPreemptRestHypS` [W]: `JPreemptRestHypM` at a schedulable current thread
  (narrower; `jPreemptRestHypS_of`), `hPre_ofZS`, `dispatch_invokeJPZS`,
  `dispatch_invokeJEPZS`. Left: the schedulable branch's budget check with an
  endpoint timeout handler outside `PPCovT` (kp5 (i)).
-/
import Fl4Proofs.P3.XTopJointPreemptM
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
`CurInv` and a schedulable current thread** [W] (kp14: `JPreemptRestHypS`
with the unschedulable case proved by `JHole.mcsPPJC`). Left: kp5 (i), the
budget check's charge with an endpoint timeout handler outside `PPCovT`
(waiting receivers, a reschedule pending or the thread queued; l4v
`check_budget`'s `charge_budget … True` → `end_timeslice` → `handle_timeout`'s
`send_fault_ipc`). -/
def JPreemptRestHypS (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAtV (L := L) arI AR s a σ → NativeScope σ →
    σ.curThread ≠ σ.idleThread → Vs.NoSwitch σ → CurScFree σ → CtOK σ → Chg σ →
    CurInv σ → Fl4Spec.schedulable σ.curThread σ = true → ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) →
    syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ (r.2.1, r.2.2) ⦄

theorem jPreemptRestHypS_of (h : JPreemptRestHypM (L := L) arI AR) : JPreemptRestHypS (L := L) arI AR :=
  fun s a σ hJ hn hi hs hf hc hg hC _ => h s a σ hJ hn hi hs hf hc hg hC

end

end

end Fl4Proofs.P3
