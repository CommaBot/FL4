/-
P3 (DESIGN.md §9): **`cur_sc_chargeable` at a preemption hole** (KENTRY-PLAN
kp13, (2b) case (b), first part).

kp11/kp12 (b): at a hole without `CurInv` whose current thread is not
schedulable and whose current SC is active, the spec's preemption path
charges the current SC (`charge_budget consumed false`). `Inv` after the
charge needs that the SC's owner is in no `inClassR` state (else its
`RelIfBound` may break: the charge can leave the head refill not ready).
For the current thread as owner kp12's `ct_not_inClassR` gives it; for any
other owner it is l4v `cur_sc_chargeable`, carried since kp13 as ScPPR's
`Chg` in `PPR0` (every thread bound to the current SC is the current thread
or inactive): `JAtZ.ppr0_start` from `CurInv`, `PPK` steps (`PPK.ina`), the
finalisations by SpecPPR's `TR.chg` and SpecPPRC (endpoint and notification
frames).

* `jAtPre_holeL`: XTopJointPreemptK's `jAtPre_holeK` with `Chg` at the hole.
* `owner_not_inClassR`: at such a hole every thread bound to the active
  current SC is in no `inClassR` state.
* `JPreemptRestHypL` [W]: `JPreemptRestHypK` at a hole with `Chg`
  (narrower; `jPreemptRestHypL_of`), `hPre_ofZL`, `dispatch_invokeJPZL` /
  `dispatch_invokeJEPZL`. Left in it as before: (b) (now with `Chg`, so the
  charge's `Inv` is provable: the owner-parametrised `charge_budget` at a
  `JHole`, kp13 section) and (2c).
-/
import Fl4Proofs.P3.XTopJointPreemptK
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **(b)'s owner fact** (module docstring): with `CtOK`, `CurScFree` and
`Chg`, an unschedulable current thread leaves every thread bound to the
active current SC outside `inClassR` (l4v `cur_sc_chargeable`). -/
theorem owner_not_inClassR {σ : Fl4Spec.State Unit} (hc : CtOK σ) (hf : CurScFree σ) (hg : Chg σ)
    (hs : Fl4Spec.schedulable σ.curThread σ = false) {u : Fl4Spec.ObjRef} {xt : Fl4Spec.Tcb}
    {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap u = some (.tcb xt)) (hl : xt.tcbSchedContext = some σ.curSc)
    (hky : σ.kheap σ.curSc = some (.schedContext y n)) (ha : Fl4Spec.scActive y = true) :
    ¬ inClassR xt.tcbState xt.tcbFault := by
  rcases hg u xt hk hl with e | e
  · subst e; exact ct_not_inClassR hc hf hs hk hl hky ha
  · intro hcl
    rw [e] at hcl
    rcases hcl with h | ⟨_, h⟩ | ⟨_, _, h, -⟩ | ⟨_, _, _, h⟩
    · cases h
    all_goals cases h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

variable (arI) in
/-- **The preemption path outside `PPCov ∨ PPCovT ∨ PPCovI` at a hole with
`CtOK`, `CurScFree` and `Chg`** [W] (kp13: `JPreemptRestHypK` narrowed by
`jAtPre_holeL`). Left: (b) no `CurInv`, current thread not schedulable,
active current SC (l4v `charge_budget` of `cur_sc`; its owner is in no
`inClassR` state by `owner_not_inClassR`), and kp5 (i) (`CurInv`, an
endpoint timeout handler with waiting receivers). -/
def JPreemptRestHypL (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAtV (L := L) arI AR s a σ → NativeScope σ →
    σ.curThread ≠ σ.idleThread → Vs.NoSwitch σ → CurScFree σ → CtOK σ → Chg σ →
    (CurInv σ ∨ Fl4Spec.schedulable σ.curThread σ = false) → ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) →
    syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ (r.2.1, r.2.2) ⦄

theorem jPreemptRestHypL_of (h : JPreemptRestHypK (L := L) arI AR) : JPreemptRestHypL (L := L) arI AR :=
  fun s a σ hJ hn hi hs hf hc _ => h s a σ hJ hn hi hs hf hc

end

end

end Fl4Proofs.P3
