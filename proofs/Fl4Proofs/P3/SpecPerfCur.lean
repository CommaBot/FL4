/-
P3 (DESIGN.md §9): **an invocation keeps the current thread**
(`perfCurKeep : PerfCurKeep`, spec-only): every outcome of the spec's
`fl4PerformInvocation` has the entry state's `curThread`.

The spec writes `curThread` only in `switchToThread`/`switchToIdleThread`,
reached from `schedule` alone. Every invocation but the Domain cap's keeps
VsDom's `schedF` (the domain schedule and `cur_thread`: AllDom's
`dke_fl4Perform`, built from the monad's combinators with one `DK` lemma per
spec function); the Domain cap's invocations change the domain schedule, so
they keep only `curThread` (`FK (·.curThread)`, the same combinators;
`set_domain` itself is `DK`). l4v: `perform_invocation` leaves `cur_thread`
alone (Syscall_AI's `pinv_tcb`-style frames, used by `handle_invocation`'s
`set_thread_state Running thread`).
-/
import Fl4Proofs.P3.AllDom
open Classical

namespace Fl4Proofs.P3.Vs
open Fl4Spec

noncomputable section

/-- `DK` keeps the current thread (`FK` form). -/
theorem DK.ctK {α : Type} {m : NonDet (State Unit) α} (h : DK m) : FK (fun σ : State Unit => σ.curThread) m :=
  fun _ _ hx => h.ct hx

theorem dk_invokeSetDomain (t : ObjRef) (d : Domain) : DK (invokeSetDomain (Z := Unit) t d) := by
  unfold invokeSetDomain archPrepareSetDomain setDomain threadSetDomain; dk_auto

theorem ct_domainSetStart (i : Nat) : FK (fun σ : State Unit => σ.curThread) (domainSetStart (Z := Unit) i) := by
  unfold domainSetStart
  refine dk_bind (dk_modify fun _ => rfl) fun _ => ?_
  refine dk_bind (dk_modify fun _ => rfl) fun _ => ?_
  refine dk_bind (dk_gets _) fun _ => ?_
  refine dk_bind (dk_modify fun _ => rfl) fun _ => ?_
  exact dk_rescheduleRequired'.ctK

theorem ct_invokeDomain (d : DomainInvocation) : FK (fun σ : State Unit => σ.curThread) (invokeDomain (Z := Unit) d) := by
  cases d with
  | invokeDomainSet t dom => exact (dk_invokeSetDomain t dom).ctK
  | invokeDomainScheduleSetStart i => exact ct_domainSetStart i
  | invokeDomainScheduleConfigure i dom dur =>
    unfold invokeDomain domainScheduleConfigure; exact dk_modify fun _ => rfl

end

end Fl4Proofs.P3.Vs

namespace Fl4Proofs.P3
open Fl4Spec Fl4Proofs.P3.Vs

/-- **An invocation keeps the current thread** (spec-only: the spec
changes `curThread` only in `switchToThread`/`switchToIdleThread`, reached
from `schedule` alone, never from `fl4PerformInvocation`; l4v:
`perform_invocation` leaves `cur_thread` alone, used by `handle_invocation`'s
`set_thread_state Running thread` and Syscall_AI's `pinv_tcb`). FL4's success
tail (`flTail`) writes the reply registers of the invoker, so the spec's
invoker must still be a TCB related at `J` (`JAtZ.flTailJ` from the current
thread). Proved: `perfCurKeep`. -/
def PerfCurKeep : Prop :=
  ∀ (blk call don : Bool) (inv : Fl4Spec.Fl4Invocation) (σ1 : Fl4Spec.State Unit) y,
    y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1 → y.2.curThread = σ1.curThread

/-- **`PerfCurKeep` holds**: every invocation but the Domain cap's keeps
`schedF` (AllDom's `dke_fl4Perform`), the Domain cap's keep `curThread`
(`ct_invokeDomain`). -/
theorem perfCurKeep : PerfCurKeep := by
  intro blk call don inv σ1 y hy
  by_cases hd : NotDomInv inv
  · exact DK.ct (m := ExceptT.run _) (dke_fl4Perform blk call don inv hd) hy
  · simp only [NotDomInv, not_forall, not_not] at hd
    obtain ⟨d, rfl⟩ := hd
    have h : FKE (fun σ : State Unit => σ.curThread)
        (fl4PerformInvocation (Z := Unit) blk call don (.invokeDomain d)) := by
      simp only [fl4PerformInvocation]
      exact dke_liftE (dk_bind (ct_invokeDomain d) fun _ => dk_pure _)
    exact h σ1 y hy

end Fl4Proofs.P3
