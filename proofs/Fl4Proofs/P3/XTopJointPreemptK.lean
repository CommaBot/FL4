/-
P3 (DESIGN.md §9): **a schedulable current thread at a preemption hole has
`CurInv`** (KENTRY-PLAN kp12, (2b) case (a)).

kp11 (a): at a hole without `CurInv` whose current thread is schedulable,
the spec's `check_budget` may `end_timeslice` the current thread and then
postpone the current SC, release-enqueueing its owner, which is not the
current thread; `Inv.rel` can break, and no `JAtZ` fact excludes it. It is
excluded by ScPPR's `CtOK` (the current thread linked to the current SC or
to none, blocked on nothing), which `PPR0` carries since kp12 (from
`Entered`/`CurInv`/`CurRun` at the invocation's start, `JAtZ.ppr0_start`;
kept by `PPK` steps and, via SpecPPR's `TR.tst`, by the finalisations:
deletion only clears links, sets states `Restart`/`Inactive`, and donates an
SC only to a reply's caller, blocked on the reply). l4v counterparts: the
current thread's SC is `cur_sc` (`cur_sc_tcb_are_bound` at the invocation;
`sched_context_donate`'s donee is the `BlockedOnReply` caller, never the
current thread, `ct_in_state activatable`).

* `curInv_of_sched`: `CtOK` and a schedulable current thread give `CurInv`
  (its SC is the current SC, active and released from the queue).
* `jAtPre_holeK`: XTopJointPreemptO's `jAtPre_holeO` with `CtOK` at the hole
  (the preemption point keeps the heap, the current thread and SC).
* `JPreemptRestHypK` [W]: `JPreemptRestHypJ` at a hole with `CtOK` and
  `CurScFree`, hence `CurInv ∨ ¬ schedulable` (stated as premise). Left:
  (b) no `CurInv`, current thread not schedulable, active current SC (charge
  through the SC's owner: needs l4v `cur_sc_chargeable`, kp12 section), and
  (2c) `CurInv`, ¬`NoTmoSend`, ¬`PPCovT`. `jPreemptRestHypK_of`,
  `hPre_ofZK`, `dispatch_invokeJPZK` / `dispatch_invokeJEPZK`.
-/
import Fl4Proofs.P3.XTopJointPreemptO
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **`CtOK` and a schedulable current thread give `CurInv`** (module
docstring). -/
theorem curInv_of_sched {σ : Fl4Spec.State Unit} (hc : CtOK σ)
    (hs : Fl4Spec.schedulable σ.curThread σ = true) : CurInv σ := by
  obtain ⟨x, scp, y, n, hk, hsc, hr, hky, ha, hq⟩ := schedulable_inv hs
  have e : scp = σ.curSc := by
    rcases (hc x hk).1 with e | e <;> rw [hsc] at e <;> cases e; rfl
  subst e
  exact ⟨⟨x, hk, hsc, NotIpcBlk.of_runnable hr⟩, ⟨y, n, hky⟩, fun _ y' n' h => by
    rw [hky] at h; cases h; exact ha, hq⟩

/-- **(b) for the current thread as the current SC's owner**: at a hole
with `CtOK` and `CurScFree`, an unschedulable current thread bound to the
active current SC is in no `inClassR` state (so `InvBut σ' ct → Inv σ'`
after the charge needs no `RelIfBound` of it). What (b) still lacks is the
same for an owner other than the current thread (l4v `cur_sc_chargeable`;
kp12 section). -/
theorem ct_not_inClassR {σ : Fl4Spec.State Unit} (hc : CtOK σ) (hf : CurScFree σ)
    (hs : Fl4Spec.schedulable σ.curThread σ = false) {xt : Fl4Spec.Tcb} {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap σ.curThread = some (.tcb xt)) (hl : xt.tcbSchedContext = some σ.curSc)
    (hky : σ.kheap σ.curSc = some (.schedContext y n)) (ha : Fl4Spec.scActive y = true) :
    ¬ inClassR xt.tcbState xt.tcbFault := fun hcl => by
  have hr := inClass_runnable hcl.cls (hc xt hk).2.2
  rw [schedulable_of hk hl hr hky ha (hf _ xt hk hl)] at hs
  cases hs

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

variable (arI) in
/-- **The preemption path outside `PPCov ∨ PPCovT ∨ PPCovI` at a hole with
`CtOK` and `CurScFree`, so with `CurInv` or an unschedulable current thread**
[W] (kp12: `JPreemptRestHypJ` narrowed by `jAtPre_holeK` and
`curInv_of_sched`). Left: (b) no `CurInv`, current thread not schedulable,
active current SC (l4v `charge_budget` of `cur_sc` through its owner under
`cur_sc_chargeable`), and kp5 (i) (`CurInv`, an endpoint timeout handler
with waiting receivers). -/
def JPreemptRestHypK (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAtV (L := L) arI AR s a σ → NativeScope σ →
    σ.curThread ≠ σ.idleThread → Vs.NoSwitch σ → CurScFree σ → CtOK σ →
    (CurInv σ ∨ Fl4Spec.schedulable σ.curThread σ = false) → ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) →
    syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ (r.2.1, r.2.2) ⦄

theorem jPreemptRestHypK_of (h : JPreemptRestHypJ (L := L) arI AR) : JPreemptRestHypK (L := L) arI AR :=
  fun s a σ hJ hn hi hs _ _ _ hc => h s a σ hJ hn hi hs hc

end

end

end Fl4Proofs.P3
