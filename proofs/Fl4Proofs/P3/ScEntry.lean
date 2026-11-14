/-
P3 (DESIGN.md §9), scheduling contexts: **the budget path at kernel entry**,
from the invariants alone.

FL4 enters the kernel through `syscall::budget_ok` (system calls and user
exceptions: `update_timestamp`, then `check_budget_restart`) or
`handle_interrupt_entry` (`update_timestamp`, then `check_budget`). Both
refine l4v's `update_time_stamp` followed by `check_budget_restart` /
`check_budget` (`budget_ok_refines`, `entry_check_budget_refines`) and end in
full `Inv`. The current-thread facts that `charge_budget_refines` took as
hypotheses come from `CurInv` (`CurInv.facts`), which is kept, or the
scheduler is asked to choose a new thread (l4v `cur_sc_tcb` is guarded by
`schact_is_rct` the same way).

`commit_time` (on the context-switch path) keeps `CurInv` and `InvBut` for
the current thread (`commit_time_cur`).

What remains as hypotheses: the clock (`hnow`), one domain (`hnd`), the
platform constants (`hmrt`, `hmb`), and the timeout-fault IPC (`hval`,
`hto`). The idle SC word is part of the relation (`SchedSpec.idleSc`).
-/
import Fl4Proofs.P3.ScTime
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **System-call entry: `budget_ok` refines `update_time_stamp;
check_budget_restart`** and ends in full `Inv`. -/
theorem budget_ok_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hC : CurInv σ)
    (hnd : Fl4Spec.numDomains = 1)
    (hnow : ar.now a ⦃ r => ∃ ms, Fl4Spec.doMachineOp (Z := Unit) Fl4Spec.getCurrentTime σ =
      ({(r.1.bv, { σ with machineState := ms })}, False) ∧ σ.curTime ≤ r.1.bv ⦄)
    (hmrt : ∀ a : A, sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hval : ∀ (s' : S) (σ' : Fl4Spec.State Unit), SchedRel st N T C c s' σ' →
      faults.valid_timeout_handler st s' (nodeW st s c layout.node.CUR_THREAD) ⦃ b =>
        Fl4Spec.isValidTimeoutHandler (Z := Unit) (nodeW st s c layout.node.CUR_THREAD).bv σ' =
          ({(b, σ')}, False) ⦄)
    (hto : ∀ (s' : S) (a' : A) (σ' : Fl4Spec.State Unit), SchedRel st N T C c s' σ' →
      NtfnStateRel N T (L.mem s') σ' → NSC N C σ' → InvBut σ' (nodeW st s c layout.node.CUR_THREAD).bv →
      faults.handle_timeout st ar s' a' (nodeW st s c layout.node.CUR_THREAD)
        (error.Fault.Timeout (L.mem s' (scW (nodeW st s c layout.node.CUR_SC) 48#u64))) ⦃ r => ∃ σ'',
        Fl4Spec.handleTimeout (Z := Unit) (nodeW st s c layout.node.CUR_THREAD).bv
          (.timeout (L.mem s' (scW (nodeW st s c layout.node.CUR_SC) 48#u64)).bv) σ' = ({((), σ'')}, False) ∧
        SchedRel st N T C c r.1 σ'' ∧ Inv σ'' ∧ NtfnStateRel N T (L.mem r.1) σ'' ∧ NSC N C σ'' ∧
        σ''.consumedTime = σ'.consumedTime ⦄) :
    syscall.budget_ok st ar s a ⦃ r => ∃ σ',
      (Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart) σ = ({(r.1, σ')}, False) ∧
      SchedRel st N T C c r.2.1 σ' ∧ Inv σ' ∧ NtfnStateRel N T (L.mem r.2.1) σ' ∧ NSC N C σ' ∧
      (σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧ (OffReady σ → OffOK σ') ⦄ := by
  unfold syscall.budget_ok
  refine WP.spec_bind (update_timestamp_refines s a σ hS hR hN hnd hnow) ?_
  rintro ⟨s1, a1⟩ ⟨σ1, h1, hS1, hR1, hN1, hI1, hC1, -, hnw, hO1⟩
  have hI1 := hI1 hI
  have hC1 := hC1 hC
  obtain ⟨hscC, hsc0, htw, hts, hact, hnr, hnb⟩ := CurInv.facts hS1 hI1 hC1
  have e_ct : nodeW st s1 c layout.node.CUR_THREAD = nodeW st s c layout.node.CUR_THREAD :=
    hnw _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD])
  have e_sc : nodeW st s1 c layout.node.CUR_SC = nodeW st s c layout.node.CUR_SC :=
    hnw _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])
  refine WP.spec_mono (check_budget_restart_refines s1 a1 σ1 hS1 hR1 hN1 hI1 hscC hsc0 htw hts
    hS1.idle hact hnr hnb hnd (hmrt a1) (hmb a1) (by rw [e_ct]; exact hval)
    (fun s' σ' => by rw [e_ct, e_sc]; exact hto s' a1 σ')) ?_
  rintro r ⟨σ', h2, hS2, hI2, hR2, hN2, hC2, hO2⟩
  exact ⟨σ', by rw [nd_bind_one h1]; exact h2, hS2, hI2, hR2, hN2, hC2 hC1, fun ho => hO2 (hO1 ho)⟩

/-- **Interrupt entry: `update_timestamp; check_budget` refines
`update_time_stamp; check_budget`** and ends in full `Inv`. -/
theorem entry_check_budget_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hC : CurInv σ)
    (hnd : Fl4Spec.numDomains = 1)
    (hnow : ar.now a ⦃ r => ∃ ms, Fl4Spec.doMachineOp (Z := Unit) Fl4Spec.getCurrentTime σ =
      ({(r.1.bv, { σ with machineState := ms })}, False) ∧ σ.curTime ≤ r.1.bv ⦄)
    (hmrt : ∀ a : A, sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hval : ∀ (s' : S) (σ' : Fl4Spec.State Unit), SchedRel st N T C c s' σ' →
      faults.valid_timeout_handler st s' (nodeW st s c layout.node.CUR_THREAD) ⦃ b =>
        Fl4Spec.isValidTimeoutHandler (Z := Unit) (nodeW st s c layout.node.CUR_THREAD).bv σ' =
          ({(b, σ')}, False) ⦄)
    (hto : ∀ (s' : S) (a' : A) (σ' : Fl4Spec.State Unit), SchedRel st N T C c s' σ' →
      NtfnStateRel N T (L.mem s') σ' → NSC N C σ' → InvBut σ' (nodeW st s c layout.node.CUR_THREAD).bv →
      faults.handle_timeout st ar s' a' (nodeW st s c layout.node.CUR_THREAD)
        (error.Fault.Timeout (L.mem s' (scW (nodeW st s c layout.node.CUR_SC) 48#u64))) ⦃ r => ∃ σ'',
        Fl4Spec.handleTimeout (Z := Unit) (nodeW st s c layout.node.CUR_THREAD).bv
          (.timeout (L.mem s' (scW (nodeW st s c layout.node.CUR_SC) 48#u64)).bv) σ' = ({((), σ'')}, False) ∧
        SchedRel st N T C c r.1 σ'' ∧ Inv σ'' ∧ NtfnStateRel N T (L.mem r.1) σ'' ∧ NSC N C σ'' ∧
        σ''.consumedTime = σ'.consumedTime ⦄) :
    (do
      let (s1, a1) ← sched.update_timestamp st ar s a
      sched.check_budget st ar s1 a1) ⦃ r => ∃ σ',
      (Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudget) σ = ({(r.1, σ')}, False) ∧
      SchedRel st N T C c r.2.1 σ' ∧ Inv σ' ∧ NtfnStateRel N T (L.mem r.2.1) σ' ∧ NSC N C σ' ∧
      (σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧ (OffReady σ → OffOK σ') ⦄ := by
  refine WP.spec_bind (update_timestamp_refines s a σ hS hR hN hnd hnow) ?_
  rintro ⟨s1, a1⟩ ⟨σ1, h1, hS1, hR1, hN1, hI1, hC1, -, hnw, hO1⟩
  have hI1 := hI1 hI
  have hC1 := hC1 hC
  obtain ⟨hscC, hsc0, htw, hts, hact, hnr, hnb⟩ := CurInv.facts hS1 hI1 hC1
  have e_ct : nodeW st s1 c layout.node.CUR_THREAD = nodeW st s c layout.node.CUR_THREAD :=
    hnw _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD])
  have e_sc : nodeW st s1 c layout.node.CUR_SC = nodeW st s c layout.node.CUR_SC :=
    hnw _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])
  have hkp : ∃ x n, σ1.kheap (nodeW st s1 c layout.node.CUR_SC).bv = some (.schedContext x n) := by
    obtain ⟨Q, R, hc, hs⟩ := hS1.lists
    obtain ⟨x, n, hk, -⟩ := hs.scs _ hscC
    exact ⟨x, n, hk⟩
  refine WP.spec_mono (check_budget_refines s1 a1 σ1 hS1 hR1 hN1 hI1 hscC hsc0 htw hts
    hS1.idle hact hnr hnb hnd (hmrt a1) (hmb a1) (by rw [e_ct]; exact hval)
    (fun s' σ' => by rw [e_ct, e_sc]; exact hto s' a1 σ')) ?_
  rintro r ⟨σ', h2, hS2, hI2, hR2, hN2, hK, hO2⟩
  exact ⟨σ', by rw [nd_bind_one h1]; exact h2, hS2, hI2, hR2, hN2, hK.imp id fun hK => hC1.keeps hK hkp,
    fun ho => hO2 (hO1 ho)⟩

/-- **`commit_time` keeps `CurInv`** (and, as `commit_time_refines`, `Inv`
except for the current thread). -/
theorem commit_time_cur {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hC : CurInv σ) (hoff : OffOK σ)
    (hmrt : sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    sched.commit_time st ar s a ⦃ s' => ∃ σ', Fl4Spec.commitTime (Z := Unit) σ = ({((), σ')}, False) ∧
      SchedRel st N T C c s' σ' ∧ NtfnStateRel N T (L.mem s') σ' ∧ NSC N C σ' ∧
      InvBut σ' (nodeW st s c layout.node.CUR_THREAD).bv ∧ CurInv σ' ⦄ := by
  obtain ⟨hscC, -, htw, -, -, hnr, -⟩ := CurInv.facts hS hI hC
  have hkp : ∃ x n, σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) := by
    obtain ⟨Q, R, hc, hs⟩ := hS.lists
    obtain ⟨x, n, hk, -⟩ := hs.scs _ hscC
    exact ⟨x, n, hk⟩
  have hown0 : ∀ x n, σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) →
      x.scTcb = some (nodeW st s c layout.node.CUR_THREAD).bv := by
    intro x n hk
    obtain ⟨Q, R, hc, hs⟩ := hS.lists
    obtain ⟨xt, hkt, hxs, -⟩ := hC.tcb
    obtain ⟨y, m, hky, hyt⟩ := hI.back _ xt _ hkt hxs
    rw [hs.curSc, hk] at hky; cases hky
    rw [hyt, hs.curThread]
  refine WP.spec_mono (commit_time_refines s a σ hS hR hN hI hscC hown0 hS.idle hnr hoff hmrt hmb) ?_
  rintro s' ⟨σ', h1, h2, h3, h4, h5, hK, -⟩
  exact ⟨σ', h1, h2, h3, h4, h5, hC.keeps hK hkp⟩

end

end

end Fl4Proofs.P3.Sched
