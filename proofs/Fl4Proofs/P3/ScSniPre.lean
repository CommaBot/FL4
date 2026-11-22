/-
P3 (DESIGN.md §9), scheduler (g6b, INV-PLAN §1.U3L.H): **when the spec's
`set_next_interrupt` succeeds**, and its single outcome.

* `SniPre σ`: the current thread and the release-queue head are TCBs bound to
  an SC with refills: exactly what l4v's `set_next_interrupt` reads with
  `assert_opt` / `get_refill_head` (Fl4Spec/Schedule.lean:78).
* `sniPre_of`: `SniPre` from `SchedRel`, `Inv`, `CurInv` (the state after
  `switch_sched_context`, where `tail_refines` programs the timer): the current
  SC is active (`CurInv.active`) or the idle SC, configured (`ScRelW.idle`);
  active SCs have refills (`Inv.ne`); the release head by `Inv.rel`.
* `SetDlDet` [P]: the opaque timer operation `setDeadlineImpl` has at most one
  outcome (l4v: `setDeadline` is a `machine_op_lift` of an underspecified
  operation; the C kernel writes the TSC deadline MSR). A statement about the
  opaque machine operation only (no kernel state).
* `setNextInterrupt_one`: under `SetDlDet` and `SniPre σ` the spec's
  `setNextInterrupt` has one outcome, `σ` with another machine state.
-/
import Fl4Proofs.P3.ScAwaken
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- **What the spec's `setNextInterrupt` needs** (module docstring). -/
def SniPre (σ : State Unit) : Prop :=
  (∃ xt p y n, σ.kheap σ.curThread = some (.tcb xt) ∧ xt.tcbSchedContext = some p ∧
    σ.kheap p = some (.schedContext y n) ∧ y.scRefills ≠ []) ∧
  ∀ u, σ.releaseQueue.head? = some u → ∃ xt p y n, σ.kheap u = some (.tcb xt) ∧ xt.tcbSchedContext = some p ∧
    σ.kheap p = some (.schedContext y n) ∧ y.scRefills ≠ []

/-- **[P] The timer's opaque `setDeadlineImpl` has at most one outcome**
(module docstring). -/
def SetDlDet : Prop :=
  ∀ (d : Word64) (mr : MachineStateRest) (x y : Unit × MachineStateRest),
    x ∈ (setDeadlineImpl d mr).1 → y ∈ (setDeadlineImpl d mr).1 → x = y

theorem selectF_sni {σ α : Type} (a : α) (s : σ) :
    NonDet.selectF (σ := σ) ({a}, False) s = ({(a, s)}, False) := by
  unfold NonDet.selectF
  refine Prod.ext ?_ rfl
  ext x
  simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact Prod.ext h1 h2
  · rintro rfl; exact ⟨rfl, rfl⟩

theorem nd_modify_bind' {σ β : Type} (g : σ → σ) (f : Unit → NonDet σ β) (s : σ) :
    (NonDet.modify g >>= f) s = f () (g s) :=
  nd_bind_one (m := NonDet.modify g) (s := s) (s' := g s) (a := ()) rfl f

theorem getTcbObjRef_eq' {σ : State Unit} {p : ObjRef} {x : Tcb} (f : Tcb → Option ObjRef)
    (hk : σ.kheap p = some (.tcb x)) : getTcbObjRef (Z := Unit) f p σ = ({(f x, σ)}, False) := threadGet_eq f hk

theorem setDeadline_one (hD : SetDlDet) (d : Word64) (ms : MachineState) :
    ∃ ms', setDeadline d ms = ({((), ms')}, False) := by
  obtain ⟨mr', hi⟩ : ∃ mr', ignoreFailure (setDeadlineImpl d) ms.machineStateRest = ({((), mr')}, False) := by
    unfold ignoreFailure
    by_cases h0 : (setDeadlineImpl d ms.machineStateRest).1 = ∅
    · exact ⟨_, by rw [if_pos h0]⟩
    · obtain ⟨⟨u, mr'⟩, hx⟩ := Set.nonempty_iff_ne_empty.2 h0
      refine ⟨mr', ?_⟩
      rw [if_neg h0]
      refine Prod.ext ?_ rfl
      ext y
      constructor
      · intro hy; exact Set.mem_singleton_iff.2 (hD d _ y _ hy hx)
      · intro hy; rw [Set.mem_singleton_iff.1 hy]; exact hx
  refine ⟨{ ms with machineStateRest := mr' }, ?_⟩
  unfold setDeadline machineOpLift machineRestLift
  rw [nd_gets_bind, hi, nd_bind_one (selectF_sni _ _)]
  dsimp only
  rw [nd_modify_bind']
  rfl

theorem doMachineOp_one {α : Type} {mop : NonDet MachineState α} {σ : State Unit} {v : α}
    {ms' : MachineState} (h : mop σ.machineState = ({(v, ms')}, False)) :
    doMachineOp (Z := Unit) mop σ = ({(v, { σ with machineState := ms' })}, False) := by
  unfold doMachineOp
  rw [nd_gets_bind, h, nd_bind_one (selectF_sni _ _)]
  dsimp only
  rw [nd_modify_bind']
  rfl

/-- **The spec's `setNextInterrupt` has one outcome** under `SetDlDet` and
`SniPre` (module docstring). -/
theorem setNextInterrupt_one (hD : SetDlDet) {σ : State Unit} (hP : SniPre σ) :
    ∃ ms', setNextInterrupt (Z := Unit) σ = ({((), { σ with machineState := ms' })}, False) := by
  obtain ⟨⟨xt, p, y, n, hkt, hsc, hky, hne⟩, hrq⟩ := hP
  have hdm : ∀ X : Word64, ∃ ms', doMachineOp (Z := Unit) (setDeadline X) σ =
      ({((), { σ with machineState := ms' })}, False) := fun X => by
    obtain ⟨ms', h⟩ := setDeadline_one hD X σ.machineState
    exact ⟨ms', doMachineOp_one h⟩
  have hao : ∀ q : ObjRef, NonDet.assertOpt (σ := State Unit) (some q) σ = ({(q, σ)}, False) := fun _ => rfl
  unfold setNextInterrupt
  rw [nd_gets_bind, nd_gets_bind]
  rw [nd_bind_one (getTcbObjRef_eq' _ hkt), hsc, nd_bind_one (hao p), nd_bind_one (getRefillHead_eq hky hne),
    nd_pure_bind']
  by_cases hnd : numDomains > 1 <;> simp only [hnd, ↓reduceIte]
  on_goal 1 => rw [nd_gets_bind, nd_pure_bind']
  on_goal 2 => rw [nd_pure_bind']
  all_goals
    rw [nd_gets_bind]
    by_cases hq : σ.releaseQueue = []
    · rw [if_pos hq, nd_pure_bind']; exact hdm _
    · obtain ⟨u, hu⟩ : ∃ u, σ.releaseQueue.head? = some u := by
        cases e : σ.releaseQueue with
        | nil => exact absurd e hq
        | cons u l => exact ⟨u, rfl⟩
      obtain ⟨xu, q, z, m, hku, hscu, hkz, hnez⟩ := hrq u hu
      rw [if_neg hq, hu]
      show ∃ ms', (getTcbObjRef (Z := Unit) Tcb.tcbSchedContext u >>= _) σ = _
      rw [nd_bind_one (getTcbObjRef_eq' _ hku), hscu, nd_bind_one (hao q), nd_bind_one (getRefillHead_eq hkz hnez),
        nd_pure_bind']
      exact hdm _

end Spec

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **`SniPre` after `switch_sched_context`** (module docstring). -/
theorem sniPre_of {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hI : Inv σ) (hC : CurInv σ) : SniPre σ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  refine ⟨?_, fun u hu => ?_⟩
  · obtain ⟨xt, hkt, hsct, -⟩ := hC.tcb
    obtain ⟨y, n, hky⟩ := hC.sc
    refine ⟨xt, σ.curSc, y, n, hkt, hsct, hky, hI.ne _ y n hky ?_⟩
    by_cases hid : σ.curSc = σ.idleSc
    · obtain ⟨x', hk', -, -, hsc', -⟩ := hs.tcb _ hc.curT
      rw [← hs.curThread, hkt] at hk'; cases hk'
      rw [hsct] at hsc'
      obtain ⟨h0, hbv⟩ := optRef_some hsc'.symm
      obtain ⟨y', n', hky', hr⟩ := hs.scs _ (hs.scMem _ hc.curT h0)
      rw [hbv, hky] at hky'; cases hky'
      have h1 := hr.idle (hbv.trans hid)
      rw [hr.max] at h1
      simp only [Fl4Spec.scActive, Fl4Spec.activeSc, decide_eq_true_eq]; omega
    · exact hC.active hid y n hky
  · obtain ⟨xu, p, y, n, h1, h2, -, h4, h5⟩ := hI.rel u (List.mem_of_mem_head? hu)
    exact ⟨xu, p, y, n, h1, h2, h4, hI.ne p y n h4 h5⟩

end

end
end Fl4Proofs.P3.Sched
