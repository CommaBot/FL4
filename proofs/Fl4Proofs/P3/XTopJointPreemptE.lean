/-
P3 (DESIGN.md §9): **the preemption path's schedulable branch with a
sufficient head refill** (KENTRY-PLAN kp14, (2c) part): `check_budget`
returns `true` without a charge on both sides when the head refill can pay
the consumed time, whatever the timeout handler; XTopJointPreemptZ's
`JHole.mcsPPJZ` asked `PPCov ∨ PPCovT` only for its charging branch.

* `check_budget_suffT`: FL4's `check_budget` returns `true` at a sufficient
  head (XTopJointBudgetOk's `check_budgetT`, the other branch excluded by
  `sufficient_refines` and `getScRefillSufficient_eq`).
* `JHole.mcsPPJS`: `mcs_preemption_point` at a shifted hole with `CurInv`, a
  non-idle schedulable current thread and a sufficient head: no change, `JAt`
  by `JHole.offOK_suff` and `JHole.toJ`.
* `JPreemptRestHypE` [W]: `JPreemptRestHypS` at an insufficient head
  (narrower; `jPreemptRestHypE_of`), `hPre_ofZE`, `dispatch_invokeJPZE`,
  `dispatch_invokeJEPZE`. Left: exactly the budget check's charge with an
  endpoint timeout handler outside `PPCovT` (kp5 (i)).
-/
import Fl4Proofs.P3.XTopJointPreemptS
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **`check_budget` at a sufficient head returns `true`** (module docstring). -/
theorem check_budget_suffT {N T C : Set U64} {c : U64} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hS : SchedRel st N T C c s σ) (hscC : nodeW st s c layout.node.CUR_SC ∈ C)
    (hact : (nodeW st s c layout.node.CUR_SC).bv ≠ σ.idleSc → ∀ x n,
      σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) → Fl4Spec.scActive x = true)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hsuf : ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
      Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true) :
    sched.check_budget st ar s a ⦃ r => r.1 = true ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  unfold sched.check_budget
  step with sched.cur_sc.spec' as ⟨sc', hsc'⟩
  step with sched.consumed.spec' as ⟨cn, hcn⟩
  rw [hc.cur] at hsc' hcn
  subst hsc' hcn
  have hax : Fl4Spec.scActive x = true := by
    by_cases hi : (nodeW st s c layout.node.CUR_SC).bv = σ.idleSc
    · exact hx.active_of_rmax (hx.idle hi)
    · exact hact hi x n hk
  refine WP.spec_bind (sufficient_refines s a σ hS hscC hk hax _ hmb) ?_
  intro b hb
  by_cases hbt : b = true
  · rw [if_pos hbt, is_cur_domain_expired_eq]
    simp only [bind_ok]
    exact (WP.spec_ok _).2 rfl
  · exfalso
    rw [getScRefillSufficient_eq hk (by rw [(hx.strong hax).refills]; exact refills_ne (hx.strong hax).wf)] at hb
    have eb := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hb))).1
    exact hbt (eb.symm.trans (by rw [← hs.consumed]; exact hsuf x n (by rw [hs.curSc]; exact hk)))

end

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

variable (arI) in
/-- **The preemption path outside `PPCov ∨ PPCovT ∨ PPCovI` at a hole with
`CurInv` and a schedulable current thread** [W] (kp14: `JPreemptRestHypE`
with the unschedulable case proved by `JHole.mcsPPJC`). Left: kp5 (i), the
budget check's charge with an endpoint timeout handler outside `PPCovT`
(waiting receivers, a reschedule pending or the thread queued; l4v
`check_budget`'s `charge_budget … True` → `end_timeslice` → `handle_timeout`'s
`send_fault_ipc`). -/
def JPreemptRestHypE (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAtV (L := L) arI AR s a σ → NativeScope σ →
    σ.curThread ≠ σ.idleThread → Vs.NoSwitch σ → CurScFree σ → CtOK σ → Chg σ →
    CurInv σ → Fl4Spec.schedulable σ.curThread σ = true →
    ¬ (∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
      Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true) →
    ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) →
    syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ (r.2.1, r.2.2) ⦄

theorem jPreemptRestHypE_of (h : JPreemptRestHypS (L := L) arI AR) : JPreemptRestHypE (L := L) arI AR :=
  fun s a σ hJ hn hi hs hf hc hg hC hsc _ => h s a σ hJ hn hi hs hf hc hg hC hsc

end

end

end Fl4Proofs.P3
