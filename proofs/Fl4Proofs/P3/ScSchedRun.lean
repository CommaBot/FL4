/-
P3 (DESIGN.md §9), scheduler: **the current thread runnable or idle after
`sc_and_timer`** (`RunW.scAndTimer`), spec side only: `sc_and_timer` keeps
the current thread (`nkt_scAndTimer`), the idle thread (`ik_scAndTimer`) and
every thread's state (`schs_scAndTimer`).
-/
import Fl4Proofs.P3.ScSchedSpec
import Fl4Proofs.P3.ScFieldKeep
import Fl4Proofs.P3.ScScheduleTop
open Classical

namespace Fl4Proofs.P3.Sched
open Fl4Spec

noncomputable section

theorem nkt_doMachineOp {α : Type} {mop : NonDet MachineState α} (h : MK mop) :
    NKT (doMachineOp (Z := Unit) mop) := by
  intro σ x hx
  obtain ⟨ms, hms, e⟩ := doMachineOp_mem2 (r := x.1) (σ' := x.2) hx
  rw [e]
  exact ScTKw.of_keep ⟨rfl, h _ _ hms, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem fk_doMachineOp {α : Type} (mop : NonDet MachineState α) : FKA (doMachineOp (Z := Unit) mop) := by
  intro σ x hx
  obtain ⟨ms, -, e⟩ := doMachineOp_mem2 (r := x.1) (σ' := x.2) hx
  rw [e]
  exact ⟨rfl, rfl, rfl⟩

/-- Every outcome keeps the idle thread and the idle SC. -/
def IKA {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, x ∈ (m σ).1 → x.2.idleThread = σ.idleThread ∧ x.2.idleSc = σ.idleSc

theorem IKA.of_fk {α : Type} {m : NonDet (State Unit) α} (h : FKA m) : IKA m := fun σ x hx => (h σ x hx).2

theorem ik_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : IKA m)
    (hg : ∀ a, IKA (g a)) : IKA (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact ⟨(hg y.1 y.2 x hx).1.trans (hm σ y hy).1, (hg y.1 y.2 x hx).2.trans (hm σ y hy).2⟩

theorem ik_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : IKA m)
    (hg : ∀ a, IKA (g a)) : IKA (NonDet.bind m g) := ik_bind hm hg

theorem ik_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : IKA m) : IKA (NonDet.when P m) := by
  unfold NonDet.when
  split
  · exact h
  · exact IKA.of_fk (fk_pure' _)

theorem ik_modify {g : State Unit → State Unit} (hg : ∀ σ, (g σ).idleThread = σ.idleThread ∧ (g σ).idleSc = σ.idleSc) :
    IKA (NonDet.modify g) := by
  intro σ x hx
  rw [Set.mem_singleton_iff.1 hx]
  exact hg σ

theorem ik_scAndTimer : IKA (scAndTimer (Z := Unit)) := by
  unfold scAndTimer switchSchedContext ifConstantBandwidthRefillUnblockCheck setNextInterrupt getTcbObjRef
  repeat' (first
    | (with_reducible refine ik_bind ?_ (fun _ => ?_))
    | (with_reducible refine ik_bind' ?_ (fun _ => ?_))
    | (with_reducible apply ik_when)
    | ((with_reducible apply ik_modify); intro _; exact ⟨rfl, rfl⟩)
    | with_reducible exact IKA.of_fk (fk_gets _) | with_reducible exact IKA.of_fk (fk_assertOpt _)
    | with_reducible exact IKA.of_fk (fk_getSchedContext _) | with_reducible exact IKA.of_fk (fk_threadGet _ _)
    | (apply IKA.of_fk; (repeat (first | exact fk_doMachineOp _ | fk_step | fk_unf)); done))

theorem nkt_scAndTimer : NKT (scAndTimer (Z := Unit)) := by
  unfold scAndTimer switchSchedContext ifConstantBandwidthRefillUnblockCheck setNextInterrupt getTcbObjRef getRefillHead
  repeat (first | exact nkt_doMachineOp (mk_setDeadline _) | exact nkt_ifCondRefillUnblockCheck _ _ _ | nkt_step2)

/-- **`RunW` across `sc_and_timer`** from the state after `schedule`'s
branch (the action reset to resume). -/
theorem RunW.scAndTimer {σ3 σ' : State Unit} (h : RunW σ3)
    (he : Fl4Spec.scAndTimer (Z := Unit) { σ3 with schedulerAction := .resumeCurThread } = ({((), σ')}, False)) :
    RunW σ' := by
  have hm : ((), σ') ∈ (Fl4Spec.scAndTimer (Z := Unit) { σ3 with schedulerAction := .resumeCurThread }).1 := by
    rw [he]; exact Set.mem_singleton _
  have hK := (schs_scAndTimer _ _ hm).1
  have hct : σ'.curThread = σ3.curThread := (nkt_scAndTimer _ _ hm).ct
  have hid : σ'.idleThread = σ3.idleThread := (ik_scAndTimer _ _ hm).1
  rcases h with h | h
  · refine Or.inl fun x hx => ?_
    have hx' : σ'.kheap σ3.curThread = some (.tcb x) := by rw [← hct]; exact hx
    have hk := hK.kh σ3.curThread
    rw [hx'] at hk
    change OTK False (σ3.kheap σ3.curThread) (some (.tcb x)) at hk
    cases h0 : σ3.kheap σ3.curThread with
    | none => rw [h0] at hk; exact hk.elim
    | some o =>
      rw [h0] at hk
      rcases hk with e | ⟨y, z, e1, e2, -, hs⟩ | ⟨_, _, _, -, e⟩ | ⟨_, _, -, e, -⟩ | ⟨_, _, -, e, -⟩
      · subst e; exact h x h0
      · cases e2
        rcases hs with hs | ⟨hf, -⟩
        · subst e1; rw [hs]; exact h y h0
        · exact hf.elim
      all_goals cases e
  · exact Or.inr (by rw [hct, hid]; exact h)

end

end Fl4Proofs.P3.Sched
