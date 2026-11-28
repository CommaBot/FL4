/-
P3 (DESIGN.md §9), scheduler: **`schedule` refines l4v's up to the FPU**
(KENTRY-PLAN.md sch4 (A)): ScScheduleTop's chain (`schedule_choose_new_thread_refinesF`,
`sw_refinesF`, `cn_refinesF`, `switch_branch_refinesF`, `schedule_refinesWPF`)
with the arch hypothesis `ArchSwF` [P] (ScArchF) in place of `ArchSwF`,
whose `ArchKeeps` heap equality is false whenever the spec has an FPU
owner. Every post's `HeapEqUpToFpu σ σ'` becomes `HeapEqUpToFpu σ σ'`; the
switching lemmas take `FpuOwnOK` at the switch state (`ArchSwF`'s [J]
side condition), carried from the state after the TCB timers
(`schedule_refinesWPF`'s `hPo`: the fire predicate implies it) across
`awaken` (`ow_awaken`, `Calm`'s heap equality) and the queue operations
(`ow_tcbSchedAction`, `QChange`). `schedule_refinesWPF` supersedes
`schedule_refinesWPF` (same post).
-/
import Fl4Proofs.P3.ScArchF
import Fl4Proofs.P3.G7cCr3K
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

/-- An outcome of a `CRK` spec function keeps the ASID table (g7d: frames
`VsRootOK` to the switch states). -/
theorem asid_of_crk {α : Type} {m : Fl4Spec.NonDet (Fl4Spec.State Unit) α} (h : Vs.CRK m)
    {σ σ' : Fl4Spec.State Unit} {a : α} {X : Prop} (he : m σ = ({(a, σ')}, X)) :
    σ'.archState.x64AsidTable = σ.archState.x64AsidTable := by
  have e := h σ (a, σ') (by rw [he]; exact Set.mem_singleton _)
  exact congrArg (fun q => q.2.1) e

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **`schedule_choose_new_thread` refines l4v's**, in the domain scope
(domain time nonzero: the domain does not end), up to the final
`set_scheduler_action resume_cur_thread`, which FL4 does in `schedule`. -/
theorem schedule_choose_new_thread_refinesF {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hvm : ∀ t ∈ T, vspace.set_vm_root st ar s a t ⦃ r => ∃ σ1, Fl4Spec.archSwitchToThread (Z := Unit) t.bv σ =
      ({((), σ1)}, False) ∧ SchedRel st N T C c r.1 σ1 ∧ NtfnStateRel N T (L.mem r.1) σ1 ∧ ArchKeepsF σ σ1 ⦄)
    (hvmi : vspace.set_kernel_vm_root st ar s a ⦃ r => ∃ σ1, Fl4Spec.archSwitchToIdleThread (Z := Unit) σ =
      ({((), σ1)}, False) ∧ SchedRel st N T C c r.1 σ1 ∧ NtfnStateRel N T (L.mem r.1) σ1 ∧ ArchKeeps σ σ1 ⦄)
    (hdt : σ.domainTime ≠ 0) :
    sched.schedule_choose_new_thread st ar s a ⦃ r => ∃ σ', Fl4Spec.scheduleChooseNewThread (Z := Unit) σ =
      ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧ TK σ σ' ∧ WritesIn st s r.1 (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  unfold sched.schedule_choose_new_thread
  step with sched.domain_time.spec2 as ⟨i, hi⟩
  have hi0 : i ≠ 0#u64 := by
    intro e; apply hdt; rw [hs.domTime, ← hi, e]; rfl
  simp only [hi0, ↓reduceIte, bind_ok]
  refine WP.spec_mono (choose_thread_refinesF s a σ hS hR hN hI hvm hvmi (by rw [← hs.idleTh])) ?_
  rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11, h12⟩
  refine ⟨σ', ?_, h2, h3, h4, h5, h6, h7, h8, h9, h11, h12⟩
  unfold Fl4Spec.scheduleChooseNewThread
  rw [nd_gets_bind]
  unfold Fl4Spec.NonDet.when
  rw [if_neg hdt, nd_bind_one (show Fl4Spec.NonDet.pure (σ := Fl4Spec.State Unit) () σ = ({((), σ)}, False) from rfl),
    nd_bind_one h1]
  rfl
/-- The switch-thread branch's direct switch: `guarded_switch_to` of a
schedulable thread, then `resume_cur_thread`. -/
theorem sw_refinesF {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hA : ArchSwF st ar N T C c) (hfo : FpuOwnOK σ) (hvr : VsRootOK T σ) {t : U64} (ht : t ∈ T) (hsch : Fl4Spec.schedulable t.bv σ = true) :
    sched.switch_to_thread st ar s a t ⦃ r => ∃ σ', (do
        Fl4Spec.guardedSwitchTo (Z := Unit) t.bv
        Fl4Spec.setSchedulerAction .resumeCurThread) σ =
      ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧ TK σ σ' ∧ WritesIn st s r.1 (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, hk, hd, -, -, -⟩ := hs.tcb t ht
  obtain ⟨x', scp, -, -, hk', hsc, -⟩ := schedulable_inv hsch
  rw [hk] at hk'; cases hk'
  refine WP.spec_mono (switch_to_thread_refinesF s a σ hS hR hN ht (hA.1 s a σ hS hR hfo hvr t ht)) ?_
  rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11, h12⟩
  refine ⟨σ', ?_, h2, h3, h4, h5 hI, Or.inr (by rw [h6]; exact hsch), h7, h8, h9, h11, h12⟩
  rw [nd_bind_one (by rw [guardedSwitchTo_eq hk hsc hsch (by rw [hd, hs.curDom.1])]; exact h1)]
  rfl

end

end

end Fl4Proofs.P3.Sched
