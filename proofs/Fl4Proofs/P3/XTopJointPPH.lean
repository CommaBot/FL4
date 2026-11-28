/-
P3 (DESIGN.md §9), scheduling contexts: **the state after a PREEMPTING
preemption point** (KENTRY-PLAN item 7, step 1: `JAtPre`).

* `nall_getsThe` (SpecFreeRet's `NAll`: every outcome satisfies `P`).
* `pp_err_eq` (spec): every `error` outcome of `preemption_point` is the
  state after its time update and its IRQ check (the only error is the final
  `whenE`; every step before it is deterministic or keeps the state).
* `JAtZ.ppJH`: from `JAtZ` (no `PPR0` needed), a preempting
  `sched.preemption_point` ends at a `JHole` (ScChargeH) whose base is the
  state after the two `WORK_UNITS` writes (XTopJointPP's `ppJD` with
  `JAtZ.timestampJH` in place of `timestampJD`), for EVERY spec `error`
  outcome (`pp_err_eq`).
* `jAtPre_hole`: every `JAtPre` state is a `JHole` (`JAtZ.ppJH`; since kp10
  `JAtPre` has no `JAt` disjunct), so the preemption path
  (`after_invocation (Err)`) can start from a `JHole`.
-/
import Fl4Proofs.P3.ScChargeH
import Fl4Proofs.P3.XTopJointCnDel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
open Fl4Spec
variable {σ' α β ε : Type}

theorem nall_getsThe {f : σ' → Option α} {s : σ'} {P : α × σ' → Prop} (h : ∀ v, P (v, s)) :
    NAll (NonDet.getsThe f) s P := by
  intro x hx
  unfold NonDet.getsThe at hx
  cases e : f s with
  | none => rw [e] at hx; exact (show False from hx).elim
  | some v => rw [e] at hx; rw [show x = (v, s) from hx]; exact h v

/-- **Every `error` outcome of the spec's preemption point** is the state
after its time update (`σ1`) and its IRQ check (`σ2`). -/
theorem pp_err_eq {σ σ1 σ2 : State Unit} {irq : Option Irq}
    (hE : updateTimeStamp (Z := Unit) σ = ({((), σ1)}, False))
    (hI : doMachineOp (Z := Unit) (getActiveIRQ true) σ1 = ({(irq, σ2)}, False)) :
    NAll (preemptionPoint (Z := Unit)).run σ (fun y => y.1 = .error () → y.2 = σ2) := by
  unfold preemptionPoint
  apply nallE_bind
  apply nall_liftE
  unfold doExtendedOp
  refine nall_bind (nall_det rfl ?_)
  refine nall_bind ?_
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨⟨u, es⟩, s1⟩ := x
  have hx1' : (u, es) = ((), σ) := hx1
  have hes : es = σ := (Prod.mk.inj hx1').2
  subst es
  have hx2' : s1 = σ := hx2
  subst s1
  refine nall_det rfl ?_
  show NAll (orChoiceE _ _ _).run { σ with exst := σ.exst } _
  unfold orChoiceE
  apply nallE_bind
  apply nall_liftE
  refine nall_det rfl ?_
  apply nallE_bind
  apply nall_liftE
  intro x hx
  obtain ⟨⟨rv, es2⟩, s2⟩ := x
  obtain ⟨-, hs2⟩ := hx
  have hs2' : s2 = σ := hs2
  subst s2
  dsimp only
  cases rv
  · exact nall_det rfl (fun h => by cases h)
  apply nallE_bind
  apply nall_liftE
  refine nall_bind (nall_det rfl ?_)
  refine nall_bind ?_
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨⟨u, es3⟩, s3⟩ := x
  have hx2' : s3 = σ := hx2
  subst s3
  refine nall_det rfl ?_
  apply nallE_bind
  apply nall_liftE
  refine nall_det hE ?_
  apply nallE_bind
  apply nall_liftE
  refine nall_det hI ?_
  apply nallE_bind
  apply nall_liftE
  refine nall_det rfl ?_
  apply nallE_bind
  apply nall_liftE
  refine nall_det rfl ?_
  apply nallE_bind
  apply nall_liftE
  refine nall_det rfl ?_
  apply nallE_bind
  apply nall_liftE
  unfold getScActive
  refine nall_getsThe (fun v => ?_)
  apply nallE_bind
  apply nall_liftE
  refine nall_det rfl ?_
  dsimp only
  unfold NonDetE.whenE
  split
  · exact nall_det rfl (fun _ => rfl)
  · exact nall_det rfl (fun _ => rfl)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **A `JAtZ` state is a `JHole` over itself.** -/
theorem JAtZ.toHole {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    JHole (L := L) arI AR Z H Cs Ac Lst D s a σ s a σ where
  j0 := J
  spec := ⟨σ.machineState, σ.curTime, σ.consumedTime, rfl, rfl⟩
  ws := P1.WritesIn.refl s _
  xtop := J.xtop
  nsc := J.nsc
  inv := J.inv
  cur := J.cur
  act := J.act
  blk := J.blk
  dbg := rfl
  dbgK := P1.DbgKeep.refl s

end

end

end Fl4Proofs.P3
