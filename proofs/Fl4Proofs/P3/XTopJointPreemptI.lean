/-
P3 (DESIGN.md §9): **the preemption path with an inactive current SC**
(KENTRY-PLAN kp8, item 7 / `JPreemptRestHypN` (b)): the third branch of
`mcs_preemption_point` (current thread not schedulable, current SC not
active: FL4 writes the node's `CONSUMED` word 0, the spec sets
`consumed_time := 0`), from ANY `JHole`, `JAtZ` after.

This is the reachable shape of kp1's "reschedule pending without `CurInv`"
case in which the thread finalised its own SC (l4v `sched_context_unbind_all_tcbs`
then `sched_context_zero_refill_max`: the current SC stays the current SC,
unbound and inactive; the same holds for an idle current thread with an
inactive idle SC). `CurInv` is not needed: the step touches one node word.

* `mem_pp_inact` / `fail_pp_inact` (spec): outcomes / failure of
  `preemption_path` in that branch.
* `JHole.mcsPPJI`: FL4's branch at a `JHole`; the end is a `JHole` over the
  same base (the time words of a hole are free), `JAtZ` by `JHole.toJ`:
  `OffOK` is vacuous at a zero consumed time and `CurOwnW` is the base's
  (same heap, current SC and release queue; its release-queue clause is
  vacuous at a zero consumed time).
* `PPCovI σ`: the branch's condition; `JPreemptRestHypI` [W]:
  `JPreemptRestHypN` outside `PPCov ∨ PPCovT ∨ PPCovI` (narrower;
  `jPreemptRestHypI_of`); `afterInv_of_mcs` (XTopJointPreemptZ's
  `afterInvJZ` from any `mcs_preemption_point` post with `JAt`),
  `hPre_ofZI`, `dispatch_invokeJPZI` / `dispatch_invokeJEPZI`.
* kp10: `JPreemptRestHypJ` [W] = `JPreemptRestHypI` at a hole whose current
  thread is not idle and with no switch pending (`JAtPre` carries both from
  the preemption point's base, XTopJointPreemptZ's `jAtPre_holeTN`;
  `jPreemptRestHypJ_of`), `hPre_ofZJ`, `dispatch_invokeJPZJ` /
  `dispatch_invokeJEPZJ`.
-/
import Fl4Proofs.P3.XTopJointPreemptZ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

theorem mem_pp_inact {σ : State Unit} {y : Unit × State Unit}
    (hs : schedulable σ.curThread σ = false)
    (hga : getScActive (Z := Unit) σ.curSc σ = ({(false, σ)}, False))
    (h2 : y ∈ (maybeHandleInterrupt (Z := Unit) true { σ with consumedTime := 0 }).1) :
    y ∈ (preemptionPath (Z := Unit) σ).1 := by
  unfold preemptionPath
  refine mem_bind_nd (x := (σ.curThread, σ)) rfl (mem_bind_nd (x := (schedulable σ.curThread σ, σ)) rfl ?_)
  show y ∈ ((if schedulable σ.curThread σ = true then (_ : SMonad Unit Unit) else _) σ).1
  rw [if_neg (by simp [hs])]
  refine mem_bind_nd (x := (σ.curSc, σ)) rfl (mem_bind_nd (x := (false, σ)) (by rw [hga]; rfl) ?_)
  show y ∈ ((if false = true then (_ : SMonad Unit Unit) else _) σ).1
  rw [if_neg (by simp)]
  exact mem_bind_nd (Set.mem_singleton _) h2

theorem fail_pp_inact {σ : State Unit}
    (hs : schedulable σ.curThread σ = false)
    (hga : getScActive (Z := Unit) σ.curSc σ = ({(false, σ)}, False))
    (h2 : (maybeHandleInterrupt (Z := Unit) true { σ with consumedTime := 0 }).2) :
    (preemptionPath (Z := Unit) σ).2 := by
  unfold preemptionPath
  refine Or.inr ⟨(σ.curThread, σ), rfl, Or.inr ⟨(schedulable σ.curThread σ, σ), rfl, ?_⟩⟩
  show ((if schedulable σ.curThread σ = true then (_ : SMonad Unit Unit) else _) σ).2
  rw [if_neg (by simp [hs])]
  refine Or.inr ⟨(σ.curSc, σ), rfl, Or.inr ⟨(false, σ), by rw [hga]; rfl, ?_⟩⟩
  show ((if false = true then (_ : SMonad Unit Unit) else _) σ).2
  rw [if_neg (by simp)]
  exact Or.inr ⟨_, Set.mem_singleton _, h2⟩

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- The state with no consumed time. -/
abbrev cons0 (σ : Fl4Spec.State Unit) : Fl4Spec.State Unit := { σ with consumedTime := 0 }

/-- **The inactive-SC branch of the preemption path** (module docstring). -/
def PPCovI (σ : Fl4Spec.State Unit) : Prop :=
  Fl4Spec.schedulable σ.curThread σ = false ∧
    ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → Fl4Spec.scActive x = false

variable (arI) in
/-- **The preemption path outside `PPCov ∨ PPCovT ∨ PPCovI`** [W] (module
docstring; `JPreemptRestHypN` narrowed by the inactive-SC branch). -/
def JPreemptRestHypI (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAtV (L := L) arI AR s a σ → NativeScope σ →
    ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) →
    syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ (r.2.1, r.2.2) ⦄

theorem jPreemptRestHypI_of (h : JPreemptRestHypN (L := L) arI AR) : JPreemptRestHypI (L := L) arI AR :=
  fun s a σ hJ hn hc => h s a σ hJ hn fun h' => hc (h'.elim Or.inl fun h2 => Or.inr (Or.inl h2))

variable (arI) in
/-- **The preemption path outside `PPCov ∨ PPCovT ∨ PPCovI` at a hole with
no switch pending and a non-idle current thread** [W] (kp10:
`JPreemptRestHypI` narrowed by `JAtPre`'s base facts, `jAtPre_holeTN`).
Left: no `CurInv` with a schedulable thread or an active current SC (l4v
`charge_budget` of an SC not owned by the current thread, after SchedContext
Unbind of the own SC or a rebind, kp8 (b')), and kp5 (i) (an endpoint
timeout handler with waiting receivers). -/
def JPreemptRestHypJ (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAtV (L := L) arI AR s a σ → NativeScope σ →
    σ.curThread ≠ σ.idleThread → Vs.NoSwitch σ → ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) →
    syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ (r.2.1, r.2.2) ⦄

theorem jPreemptRestHypJ_of (h : JPreemptRestHypI (L := L) arI AR) : JPreemptRestHypJ (L := L) arI AR :=
  fun s a σ hJ hn _ _ hc => h s a σ hJ hn hc

end

end

end Fl4Proofs.P3
